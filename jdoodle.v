// Behavioral model of MIPS - pipelined implementation

module reg_file (RR1,RR2,WR,WD,RegWrite,RD1,RD2,clock);
  input [1:0] RR1,RR2,WR;   // Register Read/Write addresses
  input [15:0] WD;          // Data to write to a register
  input RegWrite,clock;     // Control signal to write, clock signal
  output [15:0] RD1,RD2;    // Output read data from registers

  reg [15:0] Regs[0:3];     // 4 registers of 16 bits each

  assign RD1 = Regs[RR1];   // Read data from register RR1
  assign RD2 = Regs[RR2];   // Read data from register RR2

  initial Regs[0] = 0;      // Initialize register $zero to 0

  // On the negative edge of the clock, write data to register if RegWrite is enabled
  always @(negedge clock)
    if (RegWrite==1 & WR!=0) 
  Regs[WR] <= WD;     // Write WD to register WR
endmodule

// ALU Module: Performs arithmetic and logical operations
// Accepts two inputs and an operation code to produce a result and zero flag
module alu (op,a,b,result,zero);
   input [15:0] a;      // 16-bit inputs
   input [15:0] b;
   input [3:0] op;      // 4-bit ALU control signals
   output [15:0] result;// 16-bit result of the operation
   output zero;         // Flag indicating if result is zero
   
   // Instantiate ALU1 modules for each bit of the operands
   ALU1   alu0 (a[0],b[0],op[3],op[2],op[1:0],set, op[2],c1,result[0]);
   ALU1   alu1 (a[1],b[1],op[3],op[2],op[1:0],1'b0,c1,   c2,result[1]);
   ALU1   alu2 (a[2],b[2],op[3],op[2],op[1:0],1'b0,c2,   c3,result[2]);
   ALU1   alu3 (a[3],b[3],op[3],op[2],op[1:0],1'b0,c3,   c4,result[3]);
   ALU1   alu4 (a[4],b[4],op[3],op[2],op[1:0],1'b0,c4,   c5,result[4]);
   ALU1   alu5 (a[5],b[5],op[3],op[2],op[1:0],1'b0,c5,   c6,result[5]);
   ALU1   alu6 (a[6],b[6],op[3],op[2],op[1:0],1'b0,c6,   c7,result[6]);
   ALU1   alu7 (a[7],b[7],op[3],op[2],op[1:0],1'b0,c7,   c8,result[7]);
   ALU1   alu8 (a[8],b[8],op[3],op[2],op[1:0],1'b0,c8,   c9,result[8]);
   ALU1   alu9 (a[9],b[9],op[3],op[2],op[1:0],1'b0,c9,   c10,result[9]);
   ALU1   alu10 (a[10],b[10],op[3],op[2],op[1:0],1'b0,c10,c11,result[10]);
   ALU1   alu11 (a[11],b[11],op[3],op[2],op[1:0],1'b0,c11,c12,result[11]);
   ALU1   alu12 (a[12],b[12],op[3],op[2],op[1:0],1'b0,c12,c13,result[12]);
   ALU1   alu13 (a[13],b[13],op[3],op[2],op[1:0],1'b0,c13,c14,result[13]);
   ALU1   alu14 (a[14],b[14],op[3],op[2],op[1:0],1'b0,c14,c15,result[14]);
   ALUmsb alu15 (a[15],b[15],op[3],op[2],op[1:0],1'b0,c15,c16,result[15],set); // MSB bit
   
   // If all bits in result are zero, zero = 1
   nor nor1(zero, result[0],result[1],result[2],result[3],result[4],result[5],result[6],result[7],result[8],result[9],result[10],result[11],result[12],result[13],result[14],result[15]);
endmodule

// ALU1 Module: Performs single bit arithmetic and logical operations for the ALU.
module ALU1(a,b,ainvert,binvert,op,less,carryin,carryout,result);
    input a,b,less,carryin,ainvert,binvert;
    input [1:0] op;
    output carryout,result;
    
    wire a1,b1,o0,o1,o2;
    
    // Logic operations
    and g0(o0,a1,b1);
    
    or g1(o1,a1,b1);
    
    // Invert inputs based on control signals
    xor g2(b1,b,binvert),
        g3(a1,a,ainvert);

    // Full adder for addition
    full_adder FA(a1,b1,carryin,o2,carryout);
    
    // Multiplexer to select the final result based on the operation
    mux_4x1 OPMUX(o0,o1,o2,less,op[1],op[0],result);
endmodule

// ALUmsb Module: Handles the most significant bit operations in the ALU.
module ALUmsb(a,b,ainvert,binvert,op,less,carryin,carryout,result,sum);
    input a,b,less,carryin,ainvert,binvert;
    input [1:0] op;
    output carryout,result,sum;
    
    wire a1,b1,o0,o1,o2,v;
    
    // Logic operations
    and g0(o0,a1,b1);
    
    or g1(o1,a1,b1);
    
    // Invert inputs based on control signals
    xor g2(b1,b,binvert),
        g3(a1,a,ainvert);

    // Full adder for addition
    full_adder FA(a1,b1,carryin,o2,carryout);
    
    // Multiplexer to select the final result based on the operation
    mux_4x1 OPMUX(o0,o1,o2,less,op[1],op[0],result);
    
    // Compute sum for signed operations
    and g4(sum, o2);
    
    // Compute final carry out
    xor g5(v,carryin,carryout);
    
    and g6(carryout,v,op[1]);
endmodule

// Main Control Unit: Decodes the op code to generate control signals for ALU, register file, and other components
// Provides signals to determine ALU operation and register behavior.
module MainControl (Op,Control); 
  input [3:0] Op;           // Operation code
  output reg [10:0] Control; // Control signals
  
// Control bits: RegDst,ALUSrc,RegWrite,ALUOp
  always @(Op) case (Op)
    4'b0000: Control <= 11'b10010_0_0_0010; //add R-type
    4'b0001: Control <= 11'b10010_0_0_0110; //sub R-type
    4'b0010: Control <= 11'b10010_0_0_0000; //and R-type
    4'b0011: Control <= 11'b10010_0_0_0001; //or R-type
    4'b0100: Control <= 11'b10010_0_0_1100; //nor R-type
    4'b0101: Control <= 11'b10010_0_0_1101; //nand R-type
    4'b0110: Control <= 11'b10010_0_0_0111; //slt R-type
    4'b0111: Control <= 11'b01010_0_0_0010; //addi I-type
    4'b1000: Control <= 11'b01110_0_0_0010; //lw I-type
    4'b1001: Control <= 11'b01001_0_0_0010; //sw I-type
    4'b1010: Control <= 11'b00000_1_0_0110; //beq I-type
    4'b1011: Control <= 11'b00000_0_1_0110; //bne I-type
  endcase
endmodule

module CPU (clock,PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
  input clock;
  output [15:0] PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD;

  initial begin 
// Program: swap memory cells (if needed) and compute absolute value |5-7|=2
  IMemory[0]  = 16'b1000_00_01_00000000;  // lw $t1, 0($0)
  IMemory[1]  = 16'b1000_00_10_00000010;  // lw $t2, 2($0)
  IMemory[2]  = 16'b0000_00_00_00000000;  // nop
  IMemory[3]  = 16'b0000_00_00_00000000;  // nop
  IMemory[4]  = 16'b0000_00_00_00000000;  // nop
  IMemory[5]  = 16'b0110_01_10_11_000000; // slt $t3, $t1, $t2
  IMemory[6]  = 16'b0000_00_00_00000000;  // nop
  IMemory[7]  = 16'b0000_00_00_00000000;  // nop
  IMemory[8]  = 16'b0000_00_00_00000000;  // nop
  IMemory[9]  = 16'b1010_00_11_00000101;  // beq $t3, $0, IMemory[15]
  IMemory[10] = 16'b0000_00_00_00000000;  // nop
  IMemory[11] = 16'b0000_00_00_00000000;  // nop
  IMemory[12] = 16'b0000_00_00_00000000;  // nop
  IMemory[13] = 16'b1001_00_01_00000010;  // sw $t1, 2($0) 
  IMemory[14] = 16'b1001_00_10_00000000;  // sw $t2, 0($0)
  IMemory[15] = 16'b0000_00_00_00000000;  // nop
  IMemory[16] = 16'b0000_00_00_00000000;  // nop
  IMemory[17] = 16'b0000_00_00_00000000;  // nop
  IMemory[18] = 16'b1000_00_01_00000000;  // lw $t1, 0($0) 
  IMemory[19] = 16'b1000_00_10_00000010;  // lw $t2, 2($0)
  IMemory[20] = 16'b0000_00_00_00000000;  // nop
  IMemory[21] = 16'b0000_00_00_00000000;  // nop
  IMemory[22] = 16'b0000_00_00_00000000;  // nop
  IMemory[23] = 16'b0100_10_10_10_000000; // nor $t2, $t2, $t2 (sub $3, $1, $2 in twos complement)
  IMemory[24] = 16'b0000_00_00_00000000;  // nop
  IMemory[25] = 16'b0000_00_00_00000000;  // nop
  IMemory[26] = 16'b0000_00_00_00000000;  // nop
  IMemory[27] = 16'b0111_10_10_00000001;  // addi $t2, $t2, 1 
  IMemory[28] = 16'b0000_00_00_00000000;  // nop
  IMemory[29] = 16'b0000_00_00_00000000;  // nop
  IMemory[30] = 16'b0000_00_00_00000000;  // nop
  IMemory[31] = 16'b0000_01_10_11_000000; // add $t3, $t1, $t2 
 
// Data
   DMemory[0] = 5; // switch the cells and see how the simulation output changes
   DMemory[1] = 7; // (beq is taken if DMemory[0]=7; DMemory[1]=5, not taken otherwise)
  end

// Pipeline 
// IF 
   wire [15:0] PCplus2, NextPC;  // Next program counter value
   reg[15:0] PC, IMemory[0:1023], IFID_IR, IFID_PCplus2;
   alu fetch (4'b0010,PC,16'd2,PCplus2,Unused1);  // ALU to compute next PC
   branch_control BranchControl(EXMEM_Beq,EXMEM_Bne,EXMEM_Zero,branchOut); //Branch Control Unit
   mux_2x1_16bit muxBranch(PCplus2,EXMEM_Target,branchOut,NextPC); //Branch MUX
// ID
   wire [10:0] Control;
   reg IDEX_RegWrite,IDEX_MemtoReg,
       IDEX_Beq, IDEX_Bne, IDEX_MemWrite,
       IDEX_ALUSrc,  IDEX_RegDst;
   reg [3:0]  IDEX_ALUctl;
   wire [15:0] RD1,RD2,SignExtend, WD;
   reg [15:0] IDEX_PCplus2,IDEX_RD1,IDEX_RD2,IDEX_SignExt,IDEXE_IR;
   reg [15:0] IDEX_IR; // For monitoring the pipeline
   reg [1:0]  IDEX_rt,IDEX_rd;
   reg MEMWB_RegWrite; // part of MEM stage, but declared here before use (to avoid error)
   reg [1:0] MEMWB_rd; // part of MEM stage, but declared here before use (to avoid error)
   reg_file rf (IFID_IR[11:10],IFID_IR[9:8],MEMWB_rd,WD,MEMWB_RegWrite,RD1,RD2,clock);
   MainControl MainCtr (IFID_IR[15:12],Control); 
   assign SignExtend = {{8{IFID_IR[7]}},IFID_IR[7:0]}; 
// EXE
   reg EXMEM_RegWrite,EXMEM_MemtoReg,
       EXMEM_Beq, EXMEM_Bne, EXMEM_MemWrite;
   wire [15:0] Target;
   reg EXMEM_Zero;
   reg [15:0] EXMEM_Target,EXMEM_ALUOut,EXMEM_RD2;
   reg [15:0] EXMEM_IR; // For monitoring the pipeline
   reg [1:0] EXMEM_rd;
   wire [15:0] B,ALUOut;
   wire [1:0] WR;
   alu branch (4'b0010,IDEX_SignExt<<1,IDEX_PCplus2,Target,Unused2);
   alu ex (IDEX_ALUctl, IDEX_RD1, B, ALUOut, Zero);
   mux_2x1_16bit MuxB(IDEX_RD2,IDEX_SignExt,IDEX_ALUSrc,B); // ALUSrc Mux 
   mux_2x1_2bit MuxWR(IDEX_rt,IDEX_rd,IDEX_RegDst,WR);      // RegDst Mux
// MEM
   reg MEMWB_MemtoReg;
   reg [15:0] DMemory[0:1023],MEMWB_MemOut,MEMWB_ALUOut;
   reg [15:0] MEMWB_IR; // For monitoring the pipeline
   wire [15:0] MemOut;
   assign MemOut = DMemory[EXMEM_ALUOut>>1];
   always @(negedge clock) if (EXMEM_MemWrite) DMemory[EXMEM_ALUOut>>1] <= EXMEM_RD2;
// WB
   mux_2x1_16bit MuxMemtoReg(MEMWB_ALUOut, MEMWB_MemOut, MEMWB_MemtoReg, WD); // MemtoReg Mux

   initial begin
    PC = 0;
// Initialize pipeline registers
    IDEX_RegWrite=0;IDEX_MemtoReg=0;IDEX_Beq=0;IDEX_Bne=0;IDEX_MemWrite=0;IDEX_ALUSrc=0;IDEX_RegDst=0;IDEX_ALUctl=0;
    IFID_IR=0;
    EXMEM_RegWrite=0;EXMEM_MemtoReg=0;EXMEM_Beq=0;EXMEM_Bne=0;EXMEM_MemWrite=0;
    EXMEM_Target=0;
    MEMWB_RegWrite=0;MEMWB_MemtoReg=0;
   end

// Running the pipeline
   always @(negedge clock) begin 
// IF
    PC <= NextPC;
    IFID_PCplus2 <= PCplus2;
    IFID_IR <= IMemory[PC>>1];
// ID
    IDEX_IR <= IFID_IR; // For monitoring the pipeline
    {IDEX_RegDst,IDEX_ALUSrc,IDEX_MemtoReg,IDEX_RegWrite,IDEX_MemWrite,IDEX_Beq,IDEX_Bne,IDEX_ALUctl} <= Control;   
    IDEX_PCplus2 <= IFID_PCplus2;
    IDEX_RD1 <= RD1; 
    IDEX_RD2 <= RD2;
    IDEX_SignExt <= SignExtend;
    IDEX_rt <= IFID_IR[9:8];
    IDEX_rd <= IFID_IR[7:6];
// EXE
    EXMEM_IR <= IDEX_IR; // For monitoring the pipeline
    EXMEM_RegWrite <= IDEX_RegWrite;
    EXMEM_MemtoReg <= IDEX_MemtoReg;
    EXMEM_Beq   <= IDEX_Beq;
    EXMEM_Bne   <= IDEX_Bne;
    EXMEM_MemWrite <= IDEX_MemWrite;
    EXMEM_Target <= Target;
    EXMEM_Zero <= Zero;
    EXMEM_ALUOut <= ALUOut;
    EXMEM_RD2 <= IDEX_RD2;
    EXMEM_rd <= WR;
// MEM
    MEMWB_IR <= EXMEM_IR; // For monitoring the pipeline
    MEMWB_RegWrite <= EXMEM_RegWrite;
    MEMWB_MemtoReg <= EXMEM_MemtoReg;
    MEMWB_MemOut <= MemOut;
    MEMWB_ALUOut <= EXMEM_ALUOut;
    MEMWB_rd <= EXMEM_rd;
// WB
// Register write happens on neg edge of the clock (if MEMWB_RegWrite is asserted)
  end
endmodule

// Test module
module test ();
  reg clock;
  wire signed [15:0] PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD;
  CPU test_cpu(clock,PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
  always #1 clock = ~clock;
  initial begin
    $display ("  PC IFID_IR          IDEX_IR          EXMEM_IR         MEMWB_IR          WD");
    $monitor ("%3d  %b %b %b %b %2d",PC,IFID_IR,IDEX_IR,EXMEM_IR,MEMWB_IR,WD);
    clock = 1;
    #69 $finish;
  end
endmodule

/* Output:
PC   IFID_IR  IDEX_IR  EXMEM_IR MEMWB_IR  WD
  0  00000000 xxxxxxxx xxxxxxxx xxxxxxxx  x
  4  8c090000 00000000 xxxxxxxx xxxxxxxx  x
  8  8c0a0004 8c090000 00000000 xxxxxxxx  x
 12  00000000 8c0a0004 8c090000 00000000  0
 16  00000000 00000000 8c0a0004 8c090000  5
 20  00000000 00000000 00000000 8c0a0004  7
 24  012a582a 00000000 00000000 00000000  0
 28  00000000 012a582a 00000000 00000000  0
 32  00000000 00000000 012a582a 00000000  0
 36  00000000 00000000 00000000 012a582a  1
 40  11600005 00000000 00000000 00000000  0
 44  00000000 11600005 00000000 00000000  0
 48  00000000 00000000 11600005 00000000  0
 52  00000000 00000000 00000000 11600005  1
 56  ac090004 00000000 00000000 00000000  0
 60  ac0a0000 ac090004 00000000 00000000  0
 64  00000000 ac0a0000 ac090004 00000000  0
 68  00000000 00000000 ac0a0000 ac090004  4
 72  00000000 00000000 00000000 ac0a0000  0
 76  8c090000 00000000 00000000 00000000  0
 80  8c0a0004 8c090000 00000000 00000000  0
 84  00000000 8c0a0004 8c090000 00000000  0
 88  00000000 00000000 8c0a0004 8c090000  7
 92  00000000 00000000 00000000 8c0a0004  5
 96  014a5027 00000000 00000000 00000000  0
100  00000000 014a5027 00000000 00000000  0
104  00000000 00000000 014a5027 00000000  0
108  00000000 00000000 00000000 014a5027 -6
112  214a0001 00000000 00000000 00000000 -1
116  00000000 214a0001 00000000 00000000 -1
120  00000000 00000000 214a0001 00000000 -1
124  00000000 00000000 00000000 214a0001 -5
128  012a5820 00000000 00000000 00000000  0
132  xxxxxxxx 012a5820 00000000 00000000  0
136  xxxxxxxx xxxxxxxx 012a5820 00000000  0
140  xxxxxxxx xxxxxxxx xxxxxxxx 012a5820  2
*/

// Branch Control Unit
module branch_control(Beq, Bne, Zero, BranchOut);
  input Beq, Bne, Zero;
  output BranchOut;
  
  not g0(notZero, Zero); // Inverted Zero
  
  and g1(BeqOut, Beq, Zero), // And logic
      g2(BneOut, Bne, notZero);
      
  or  g3(BranchOut, BeqOut, BneOut); // Seeing valid outputs
endmodule

// Multiplexors
// 2x1 Multiplexer to select between two 2-bit inputs
module mux_2x1_2bit (I0, I1, S, out);
  input [1:0] I0;       // 2-bit inputs
  input [1:0] I1;
  input S;              // Selection signal
  output [1:0] out;     // Output

  // Generate inverted signal
  not g0(notS, S);        // notS is the inverted version of S

  // Compute AND for each input bit with S or notS
  and g1(sel0_0, I0[0], notS),
      g2(sel0_1, I0[1], notS),
      g3(sel1_0, I1[0], S),
      g4(sel1_1, I1[1], S);

  // Combine results with OR gates to form the output
  or g5(out[0], sel0_0, sel1_0),
     g6(out[1], sel0_1, sel1_1);
endmodule
 
// 2x1 Multiplexer selecting between two 16-bit inputs
module mux_2x1_16bit(I0,I1,S,out);
  input [15:0] I0;     // 16-bit Input
  input [15:0] I1;     // 16-bit Input 
  input S;             // Control signal to select between inputs
  output [15:0] out;   // 16-bit output

  // Generate the complement of the select signal
  not n1(notS,S);

  // AND gates to choose the bit of the inputs using S and notS
  and g1(t1,I0[0],notS),
      g2(t2,I0[1],notS),
      g3(t3,I0[2],notS),
      g4(t4,I0[3],notS),
      g5(t5,I0[4],notS),
      g6(t6,I0[5],notS),
      g7(t7,I0[6],notS),
      g8(t8,I0[7],notS),
      g9(t9,I0[8],notS),
      g10(t10,I0[9],notS),
      g11(t11,I0[10],notS),
      g12(t12,I0[11],notS),
      g13(t13,I0[12],notS),
      g14(t14,I0[13],notS),
      g15(t15,I0[14],notS),
      g16(t16,I0[15],notS),
      
      g17(t17,I1[0],S),
      g18(t18,I1[1],S),
      g19(t19,I1[2],S),
      g20(t20,I1[3],S),
      g21(t21,I1[4],S),
      g22(t22,I1[5],S),
      g23(t23,I1[6],S),
      g24(t24,I1[7],S),
      g25(t25,I1[8],S),
      g26(t26,I1[9],S),
      g27(t27,I1[10],S),
      g28(t28,I1[11],S),
      g29(t29,I1[12],S),
      g30(t30,I1[13],S),
      g31(t31,I1[14],S),
      g32(t32,I1[15],S);

  // OR gates to combine the results from the AND gates for each bit
  or  g33(out[0],t1,t17),
      g34(out[1],t2,t18),
      g35(out[2],t3,t19),
      g36(out[3],t4,t20),
      g37(out[4],t5,t21),
      g38(out[5],t6,t22),
      g39(out[6],t7,t23),
      g40(out[7],t8,t24),
      g41(out[8],t9,t25),
      g42(out[9],t10,t26),
      g43(out[10],t11,t27),
      g44(out[11],t12,t28),
      g45(out[12],t13,t29),
      g46(out[13],t14,t30),
      g47(out[14],t15,t31),
      g48(out[15],t16,t32);
endmodule


// Components for ALU
module half_adder(x,y,S,C);
    input x,y;
    output S,C;
         
    xor g1(S,x,y);
    
    and g2(C,x,y);
endmodule

module full_adder(x,y,z,S,C);
    input x,y,z;
    output S,C;
    wire S1,C1,C2;
    
    half_adder HA1(x,y,S1,C1);
    half_adder HA2(S1,z,S,C2);
    
    or g1(C,C1,C2);
endmodule

module mux_2x1(x,y,z,out);
    input x,y,z;
    output out;
    
    wire a,b;
    
    not notz(notz, z);
    
    and g1(a,x,notz),
        g2(b,y,z);
    
    or  g3(out,a,b);
endmodule

module mux_4x1(I0,I1,I2,I3,S1,S0,out);
    input I0,I1,I2,I3,S1,S0;
    output out;
    
    wire o1, o2;
    
    mux_2x1 MUX1(I0,I1,S0,o1);
    mux_2x1 MUX2(I2,I3,S0,o2);
    mux_2x1 MUX3(o1,o2,S1,out);
endmodule
