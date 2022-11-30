
// by Raja Batra
// December 2021
// Multicycle Processor written in System Verilog


///////////////////////////////////////////////////////////////
// testbench
//
// Expect simulator to print "Simulation succeeded"
// when the value 25 (0x19) is written to address 100 (0x64)
///////////////////////////////////////////////////////////////

module testbench();

  logic        clk;
  logic        reset;

  logic [31:0] WriteData, DataAdr;
  logic        MemWrite;
  logic [31:0] hash;

  // instantiate device to be tested
  top dut(clk, reset, WriteData, DataAdr, MemWrite);
  
  // initialize test
  initial
    begin
      hash <= 0;
      reset <= 1; # 22; reset <= 0;
    end

  // generate clock to sequence tests
  always
    begin
      clk <= 1; # 5; clk <= 0; # 5;
    end

  // check results
  always @(negedge clk)
    begin
      if(MemWrite) begin
        if(DataAdr === 100 & WriteData === 25) begin
          $display("Simulation succeeded");
 	   	  $display("hash = %h", hash);
          $stop;
        end else if (DataAdr !== 96) begin
          $display("Simulation failed");
          $stop;
        end
      end
    end

  // Make 32-bit hash of instruction, PC, ALU
  always @(negedge clk)
    if (~reset) begin
      hash = hash ^ dut.rvmulti.dp.Instr ^ dut.rvmulti.dp.PC;
      if (MemWrite) hash = hash ^ WriteData;
      hash = {hash[30:0], hash[9] ^ hash[29] ^ hash[30] ^ hash[31]};
    end

endmodule

///////////////////////////////////////////////////////////////
// top
//
// Instantiates multicycle RISC-V processor and memory
///////////////////////////////////////////////////////////////

module top(input  logic        clk, reset, 
           output logic [31:0] WriteData, DataAdr, 
           output logic        MemWrite);

  logic [31:0] ReadData;
  
  // instantiate processor and memories
  riscvmulti rvmulti(clk, reset, MemWrite, DataAdr, 
                     WriteData, ReadData);
  mem mem(clk, MemWrite, DataAdr, WriteData, ReadData);
endmodule

///////////////////////////////////////////////////////////////
// mem
//
// Single-ported RAM with read and write ports
// Initialized with machine language program
///////////////////////////////////////////////////////////////

module mem(input  logic        clk, we,
           input  logic [31:0] a, wd,
           output logic [31:0] rd);

  logic [31:0] RAM[63:0];
  
  initial
      $readmemh("riscvtest.txt",RAM);

  assign rd = RAM[a[31:2]]; // word aligned

  always_ff @(posedge clk)
    if (we) RAM[a[31:2]] <= wd;
endmodule



///////////////////////////////////////////////////////////////
// riscvmulti
//
// Multicycle RISC-V microprocessor
///////////////////////////////////////////////////////////////



module riscvmulti(input  logic        clk, reset,
                  output logic        MemWrite,
                  output logic [31:0] DataAdr, WriteData,
                  input  logic [31:0] ReadData);

  // Your code goes here
  logic       RegWrite, Jump, Zero;
  logic [1:0] ResultSrc, ALUSrcA, ALUSrcB, ImmSrc;
  logic [2:0] ALUControl;
  logic [31:0] Instr;

  controller c(clk, reset, Instr[6:0], Instr[14:12], Instr[30], Zero, ImmSrc, ALUSrcA,
                ALUSrcB, ResultSrc, AdrSrc, ALUControl, IRWrite, PCWrite, 
                RegWrite, MemWrite);
                
         
  datapath dp(clk, reset, 
              PCWrite, AdrSrc, MemWrite, IRWrite,
              ResultSrc,
              ALUControl,
              ALUSrcA, 
              ALUSrcB,
              ImmSrc,
              RegWrite,
              Zero, Instr, DataAdr, WriteData, ReadData);
              

  // Instantiate controller (from lab 5) and datapath (new for this lab)
endmodule

///////////////////////////////////////////////////////////////
// Your modules go here
///////////////////////////////////////////////////////////////


module datapath(input  logic        clk, reset,
                input  logic        PCWrite, AdrSrc, MemWrite, IRWrite,
                input  logic [1:0]  ResultSrc, 
                input  logic [2:0]  ALUControl,
                input  logic [1:0]  ALUSrcA,
                input  logic [1:0]  ALUSrcB,
                input  logic [1:0]  ImmSrc,
                input  logic        RegWrite,
  
                output logic        Zero,
                output  logic [31:0] Instr,
                output logic [31:0] DataAdr, WriteData,
                input  logic [31:0] ReadData);

        logic [31:0] PCNext, PC, OldPC, Data, A, B, E;
        logic [31:0] Anext;
        //logic [4:0] D;
        logic [31:0] ImmExt, SrcA, SrcB, ALUResult, ALUOut, Result;
    //PClogic
      flopenr #(32) pcreg(clk, PCWrite, reset, Result, PC); 
      mux2 #(32)  pcmux(PC, Result, AdrSrc, DataAdr);



    // register file logic
      flopenr #(32) rdtoInstr(clk, IRWrite,reset, ReadData, Instr); 
      flopr #(32) rdtoData(clk, reset, ReadData, Data); 

      regfile     rf(clk, RegWrite, Instr[19:15], Instr[24:20], 
                 Instr[11:7], Result, A, B);
      extend      ext(Instr[31:7], ImmSrc, ImmExt);
      flopr #(32) AtoAnext(clk, reset, A, Anext); 
      flopr #(32) btoWD(clk, reset, B, WriteData); 

    //ALUlogic
      flopenr #(32) PctoOldpc(clk, IRWrite, reset, PC, OldPC); 
      mux3 #(32) SrcAmux(PC, OldPC, Anext, ALUSrcA, SrcA);
      mux3 #(32) SrcBmux(WriteData, ImmExt, 32'd4, ALUSrcB, SrcB);
      alu alu1(SrcA, SrcB, ALUControl, ALUResult, Zero);
      flopr #(32) aluflop(clk, reset, ALUResult, ALUOut);
      mux3 #(32) resultMux(ALUOut, Data, ALUResult, ResultSrc, Result);
    
    
      


endmodule

////////

module flopenr #(parameter WIDTH = 8)
              (input logic    clk,
               input logic    en,
               input logic    reset,
               input  logic [WIDTH-1:0] d,
               output logic [WIDTH-1:0] q);
        
        always_ff@(posedge clk, posedge reset)
            if      (reset) q <= 0;
            else if (en) q<=d;
endmodule

module flopr #(parameter WIDTH = 8)
              (input  logic             clk, reset,
               input  logic [WIDTH-1:0] d, 
               output logic [WIDTH-1:0] q);

  always_ff @(posedge clk, posedge reset)
    if (reset) q <= 0;
    else       q <= d;
endmodule

module alu(input  logic [31:0] a, b,
           input  logic [2:0]  alucontrol,
           output logic [31:0] result,
           output logic        zero);

  logic [31:0] condinvb, sum;

  assign condinvb = alucontrol[0] ? ~b : b;
  assign sum = a + condinvb + alucontrol[0];

  always_comb
    case (alucontrol)
      3'b000:  result = sum;       // add
      3'b001:  result = sum;       // subtract
      3'b010:  result = a & b;     // and
      3'b011:  result = a | b;     // or
      3'b101:  result = sum[31];   // slt
      3'b111:  result = a<<b;   // sll
      default: result = 32'bx;
    endcase

  assign zero = (result == 32'b0);
endmodule
module maindec(input  logic [6:0] op,
               output logic [1:0] ResultSrc,
               output logic       MemWrite,
               output logic       Branch, ALUSrc,
               output logic       RegWrite, Jump,
               output logic [1:0] ImmSrc,
               output logic [1:0] ALUOp);

  logic [10:0] controls;

  assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
          ResultSrc, Branch, ALUOp, Jump} = controls;

  always_comb
    case(op)
    // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
      7'b0000011: controls = 11'b1_00_1_0_01_0_00_0; // lw
      7'b0100011: controls = 11'b0_01_1_1_00_0_00_0; // sw
      7'b0110011: controls = 11'b1_xx_0_0_00_0_10_0; // R-type 
      7'b1100011: controls = 11'b0_10_0_0_00_1_01_0; // beq
      7'b0010011: controls = 11'b1_00_1_0_00_0_10_0; // I-type ALU
      7'b1101111: controls = 11'b1_11_0_0_10_0_00_1; // jal
      default:    controls = 11'bx_xx_x_x_xx_x_xx_x; // non-implemented instruction
    endcase
endmodule


module regfile(input  logic        clk, 
               input  logic        we3, 
               input  logic [4:0] a1, a2, a3, 
               input  logic [31:0] wd3, 
               output logic [31:0] rd1, rd2);

  logic [31:0] rf[31:0];

  // three ported register file
  // read two ports combinationally (A1/RD1, A2/RD2)
  // write third port on rising edge of clock (A3/WD3/WE3)
  // register 0 hardwired to 0

  always_ff @(posedge clk)
    if (we3) rf[a3] <= wd3;	

  assign rd1 = (a1 != 0) ? rf[a1] : 0;
  assign rd2 = (a2 != 0) ? rf[a2] : 0;
endmodule

module extend(input  logic [31:7] instr,
              input  logic [1:0]  immsrc,
              output logic [31:0] immext);
 
  always_comb
    case(immsrc) 
               // I-type 
      2'b00:   immext = {{20{instr[31]}}, instr[31:20]};  
               // S-type (stores)
      2'b01:   immext = {{20{instr[31]}}, instr[31:25], instr[11:7]}; 
               // B-type (branches)
      2'b10:   immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0}; 
               // J-type (jal)
      2'b11:   immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0}; 
      default: immext = 32'bx; // undefined
    endcase             
endmodule



module mux2 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, 
              input  logic             s, 
              output logic [WIDTH-1:0] y);

  assign y = s ? d1 : d0; 
endmodule

module mux3 #(parameter WIDTH = 8)
             (input  logic [WIDTH-1:0] d0, d1, d2,
              input  logic [1:0]       s, 
              output logic [WIDTH-1:0] y);

  assign y = s[1] ? d2 : (s[0] ? d1 : d0); 
endmodule

///////////////////////////////////////////////////////////////

////controller//////
typedef enum logic[6:0] {r_type_op=7'b0110011, i_type_alu_op=7'b0010011, lw_op=7'b0000011, sw_op=7'b0100011, beq_op=7'b1100011, jal_op=7'b1101111} opcodetype;

module controller(input  logic       clk,
                  input  logic       reset,  
                  input  logic [6:0] op,
                  input  logic [2:0] funct3,
                  input  logic       funct7b5,
                  input  logic       Zero,
                  output logic [1:0] ImmSrc,
                  output logic [1:0] ALUSrcA, ALUSrcB,
                  output logic [1:0] ResultSrc, 
                  output logic       AdrSrc,
                  output logic [2:0] ALUControl,
                  output logic       IRWrite, PCWrite, 
                  output logic       RegWrite, MemWrite);
                  
        logic [1:0] ALUOp;
        logic and1, or1;
        
        
        mainfsm fsm1(op, clk, reset, ALUSrcA, ALUSrcB, 
                    ResultSrc, ALUOp, AdrSrc, 
                    IRWrite, PCUpdate, Branch, RegWrite, MemWrite);   
        aludec adec1(op[5], funct3, funct7b5, ALUOp, ALUControl);  
                  
        instrdec instr(op, ImmSrc);     
        and g1(and1, Zero, Branch);
        or g2(PCWrite, and1, PCUpdate);
        
endmodule

module aludec(input  logic       opb5,
              input  logic [2:0] funct3,
              input  logic       funct7b5, 
              input  logic [1:0] ALUOp,
              output logic [2:0] ALUControl);

  logic  RtypeSub;
  assign RtypeSub = funct7b5 & opb5;  // TRUE for R-type subtract instruction

  always_comb
    case(ALUOp)
      2'b00:                ALUControl = 3'b000; // addition
      2'b01:                ALUControl = 3'b001; // subtraction
      default: case(funct3) // R-type or I-type ALU
                 3'b000:  if (RtypeSub) 
                            ALUControl = 3'b001; // sub
                          else          
                            ALUControl = 3'b000; // add, addi
                 3'b010:    ALUControl = 3'b101; // slt, slti
                 3'b110:    ALUControl = 3'b011; // or, ori
                 3'b111:    ALUControl = 3'b010; // and, andi
                 3'b001:    ALUControl = 3'b111; // I added this for shift left
                 default:   ALUControl = 3'bxxx; // ???
               endcase
    endcase
endmodule


////mainfsm for controller
module mainfsm(input logic [6:0] op,
              input logic clk, 
              input logic reset,  
              output logic [1:0] ALUSrcA, ALUSrcB,
              output logic [1:0] ResultSrc, 
              output logic [1:0] ALUOp, 
              output logic       AdrSrc,
              output logic       IRWrite, PCUpdate, Branch,
              output logic       RegWrite, MemWrite);

//mainfsm
        logic [3:0] state, nextstate;
        parameter s0 = 4'b 0000;
        parameter s1 = 4'b 0001;
        parameter s2 = 4'b 0010;
        parameter s3 = 4'b 0011;
        parameter s4 = 4'b 0100;
        parameter s5 = 4'b 0101;
        parameter s6 = 4'b 0110;
        parameter s7 = 4'b 0111;
        parameter s8 = 4'b 1000;
        parameter s9 = 4'b 1001;
        parameter s10 = 4'b 1010;




        always_ff@(posedge clk, posedge reset)
		      if(reset) state<=s0;
		      else      state<=nextstate;

          always_comb
            case(state)
              s0:  nextstate = s1;

              s1:  if (op==7'b0000011) nextstate = s2;
                   else if (op ==7'b0100011) nextstate = s2;
                   else if (op == 7'b0110011) nextstate = s6;
                   else if (op == 7'b0010011) nextstate = s8;
                   else if (op == 7'b1101111) nextstate = s9;
                   else if (op == 7'b1100011) nextstate = s10;
                   else nextstate = s1;
              s2:  if (op == 7'b0000011) nextstate = s3;
                   else if (op == 7'b0100011) nextstate = s5;
                   else nextstate = s2;
              s3: nextstate = s4;
              s4: nextstate = s0;
              s5: nextstate = s0;
              s6: nextstate = s7;
              s7: nextstate = s0;
              s8: nextstate = s7;
              s9: nextstate = s7;
              s10: nextstate = s0;
              
          
          
        endcase
        
        always_comb
        
        if (state == s0)
          begin
           ALUSrcA = 00;
           ALUSrcB = 10;
           ALUOp = 00;
           ResultSrc = 10;
           PCUpdate = 1;
           AdrSrc = 0;
           IRWrite = 1;
           Branch = 0;
           RegWrite = 0;
           MemWrite = 0;     
         end
        else if (state == s1)
          begin
           ALUSrcA = 01;
           ALUSrcB = 01;
           ALUOp = 00;
           ResultSrc = 00;
           PCUpdate = 0;
           AdrSrc = 0;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 0;
           MemWrite = 0;     
         end
        else if (state == s2)
          begin
           ALUSrcA = 10;
           ALUSrcB = 01;
           ALUOp = 00;
           ResultSrc = 00;
           PCUpdate = 0;
           AdrSrc = 0;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 0;
           MemWrite = 0;     
         end
        else if (state == s3)
          begin
           ALUSrcA = 00;
           ALUSrcB = 00;
           ALUOp = 00;
           ResultSrc = 00;
           PCUpdate = 0;
           AdrSrc = 1;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 0;
           MemWrite = 0;     
         end
        else if (state == s4)
          begin
           ALUSrcA = 00;
           ALUSrcB = 00;
           ALUOp = 00;
           ResultSrc = 01;
           PCUpdate = 0;
           AdrSrc = 0;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 1;
           MemWrite = 0;     
         end
        else if (state == s5)
          begin
           ALUSrcA = 00;
           ALUSrcB = 00;
           ALUOp = 00;
           ResultSrc = 00;
           PCUpdate = 0;
           AdrSrc = 1;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 0;
           MemWrite = 1;     
         end
        else if (state == s6)
          begin
           ALUSrcA = 10;
           ALUSrcB = 00;
           ALUOp = 10;
           ResultSrc = 00;
           PCUpdate = 0;
           AdrSrc = 0;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 0;
           MemWrite = 0;     
         end
        else if (state == s7)
          begin
           ALUSrcA = 00;
           ALUSrcB = 00;
           ALUOp = 00;
           ResultSrc = 00;
           PCUpdate = 0;
           AdrSrc = 0;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 1;
           MemWrite = 0;     
         end
        else if (state == s8)
          begin
           ALUSrcA = 10;
           ALUSrcB = 01;
           ALUOp = 10;
           ResultSrc = 00;
           PCUpdate = 0;
           AdrSrc = 0;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 0;
           MemWrite = 0;     
         end
        else if (state == s9)
          begin
           ALUSrcA = 01;
           ALUSrcB = 10;
           ALUOp = 00;
           ResultSrc = 00;
           PCUpdate = 1;
           AdrSrc = 0;
           IRWrite = 0;
           Branch = 0;
           RegWrite = 0;
           MemWrite = 0;     
         end
        else if (state == s10)
          begin
           ALUSrcA = 10;
           ALUSrcB = 00;
           ALUOp = 01;
           ResultSrc = 00;
           PCUpdate = 0;
           AdrSrc = 0;
           IRWrite = 0;
           Branch = 1;
           RegWrite = 0;
           MemWrite = 0;     
         end

        

endmodule
module instrdec (input logic [6:0] op, output logic [1:0] immsrc);
    always_comb 
      casez(op)
        7'b0110011: immsrc <= 2'bxx; 
        7'b0010011: immsrc <= 2'b00; 
        7'b0000011: immsrc <= 2'b00; 
        7'b0100011: immsrc <= 2'b01; 
        7'b1100011: immsrc <= 2'b10; 
        7'b1101111: immsrc <= 2'b11; 
        default:    immsrc <= 2'bxx; 
    endcase


    
endmodule



// Describe your non-leaf cells structurally
// Describe your lef cells (mux, flop, alu, etc.) behaviorally
// Exactly follow the multicycle processor diagram
// Feel free to cut and paste from riscvsingle.sv where applicable
// Remember to declare internal signals
// Be consistent with spelling and capitalization
// Be consistent with order of signals in module declarations and instantiations
// Have fun!
