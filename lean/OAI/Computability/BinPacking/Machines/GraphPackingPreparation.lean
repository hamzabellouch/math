import Mathlib.Tactic.FinCases
import OAI.Computability.BinPacking.Machines.GraphPackingPreparationFinish

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPreparation

section

open Turing BinPackingGames.Foundations.Complexity
open GraphPackingRegisters GraphPackingProgram PackingMachineBlocks
open FiniteTapeProgram BinaryRegisterProgram

variable (fixed : InventoryData) (K : Nat)

@[simp] private theorem graphSlots_apply (i : Fin 7) : graphSlots fixed K i =
    ![.inr .input, .inr .scanScratch, .inr .scanTemporary,
      .inr .threshold, .inr .endpoints, .inr .vertices, .inr .edges] i := by
  simp only [graphSlots]
  rfl

@[simp] private theorem thresholdSlots_apply (i : Fin 3) : thresholdSlots fixed K i =
    ![.inr .threshold, .inr .decodeScratch, slots fixed K (.inl (input fixed K .k))] i := by
  simp only [thresholdSlots]
  rfl

@[simp] private theorem setup_apply (r : PackingSetupMachine.Reg (parameters fixed K)) :
    setup fixed K r = .inl (.inr (.inl r)) := rfl

def parsePhases : List (Program fixed K) :=
  [prepareGraph (graphSlots fixed K),
    tallyToBinary fixed K .vertices .n,
    tallyToBinary fixed K .edges .m,
    PackingArithmeticProgram.code (PackingFieldDecodeMachine.code (thresholdSlots fixed K))]

def parsePolynomial (_fixed : InventoryData) (_K : Nat) : Polynomial Nat :=
  Polynomial.C 6 * (Polynomial.X + 1) ^ 2 + Polynomial.C 15 * Polynomial.X + Polynomial.C 15

private def fieldTapes (x : GraphReductionInput) : Tape fixed K → List Bool
  | .inr .input => graphBits x
  | .inr .threshold => BinaryEncoding.natBits x.k
  | .inr .endpoints => GraphFieldMachine.fieldBits .endpoints x
  | .inr .vertices => List.replicate x.graph.n true
  | .inr .edges => List.replicate x.graph.edges.length true
  | _ => []

private theorem preparation_frame (x : GraphReductionInput) :
    GraphPreparationMachine.preparedTapes (graphSlots fixed K) (initialTapes fixed K x) x =
      fieldTapes fixed K x := by
  have atSlot (j : Fin 7) :
      GraphPreparationMachine.preparedTapes (graphSlots fixed K) (initialTapes fixed K x) x
        (graphSlots fixed K j) = fieldTapes fixed K x (graphSlots fixed K j) := by
    rw [GraphPreparationMachine.preparedTapes_register]
    fin_cases j <;> simp [initialTapes, fieldTapes]
  funext tape
  cases tape with
  | inl r =>
      simpa only [initialTapes, fieldTapes] using
        GraphPreparationMachine.preparedTapes_other (graphSlots fixed K)
          (initialTapes fixed K x) x (.inl r)
          (by simp) (by simp)
          (by simp) (by simp)
  | inr extra =>
      by_cases h₃ : extra = .threshold
      · subst extra; exact atSlot 3
      by_cases h₄ : extra = .endpoints
      · subst extra; exact atSlot 4
      by_cases h₅ : extra = .vertices
      · subst extra; exact atSlot 5
      by_cases h₆ : extra = .edges
      · subst extra; exact atSlot 6
      rw [GraphPreparationMachine.preparedTapes_other (graphSlots fixed K)
        (initialTapes fixed K x) x (.inr extra)
        (by simpa using h₃) (by simpa using h₄)
        (by simpa using h₅) (by simpa using h₆)]
      cases extra <;> simp_all [initialTapes, fieldTapes]

private def vertexTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  Function.update (Function.update (fieldTapes fixed K x) (.inr .vertices) [])
    (regTape fixed K (input fixed K .n)) x.graph.n.bits

private def edgeTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  Function.update (Function.update (vertexTapes fixed K x) (.inr .edges) [])
    (regTape fixed K (input fixed K .m)) x.graph.edges.length.bits

private theorem decoded_frame (x : GraphReductionInput) :
    PackingFieldDecodeMachine.decodedTapes (thresholdSlots fixed K) (edgeTapes fixed K x)
      x.k.bits [] = parsedTapes fixed K x := by
  funext tape
  rcases tape with (r | scratch) | extra
  · change _ = registerTapes (slots fixed K) (baseTapes fixed K x)
      (PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator
        (fun _ => 0) (parsedOther fixed K x)) (slots fixed K (.inl r))
    rw [registerTapes_reg]
    rcases r with (v | (setupReg | workReg)) | node
    · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
        vertexTapes, fieldTapes, regTape, slots, input,
        PackingMachineLayout.registers,
        PackingMachineLayout.values, PackingSetupMachine.input]
    · rcases setupReg with i | (o | node)
      · cases i <;> simp [PackingFieldDecodeMachine.decodedTapes,
          edgeTapes, vertexTapes, fieldTapes, regTape, slots, input,
          PackingMachineLayout.registers,
          PackingMachineLayout.values, parsedOther, PackingSetupMachine.frame,
          PackingSetupMachine.input, PackingSetupExpression.inputs]
        change Function.update (β := fun _ => List Bool) _ (thresholdSlots fixed K 2) x.k.bits
          (thresholdSlots fixed K 2) = x.k.bits
        exact Function.update_self _ _ _
      · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
          vertexTapes, fieldTapes, regTape, slots, input,
          PackingMachineLayout.registers,
          PackingMachineLayout.values, parsedOther, PackingSetupMachine.frame,
          PackingSetupMachine.input]
      · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
          vertexTapes, fieldTapes, regTape, slots, input,
          PackingMachineLayout.registers,
          PackingMachineLayout.values, parsedOther, PackingSetupMachine.frame,
          PackingSetupMachine.input]
    · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
        vertexTapes, fieldTapes, regTape, slots, input,
        PackingMachineLayout.registers,
        PackingMachineLayout.values, parsedOther, PackingSetupMachine.input]
    · simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
        vertexTapes, fieldTapes, regTape, slots, input,
        PackingMachineLayout.registers,
        PackingMachineLayout.values, PackingSetupMachine.input]
  · change _ = registerTapes (slots fixed K) (baseTapes fixed K x)
      (PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator
        (fun _ => 0) (parsedOther fixed K x)) (slots fixed K (.inr scratch))
    rw [registerTapes_scratch]
    simp [PackingFieldDecodeMachine.decodedTapes, edgeTapes,
      vertexTapes, fieldTapes, regTape, slots, PackingMachineLayout.registers]
  · change _ = PackingMachineLayout.tapes (Numerator fixed) PackingItemExpression.denominator
      (baseTapes fixed K x) (fun _ => 0) (parsedOther fixed K x) (.inr extra)
    rw [PackingMachineLayout.tapes_extra]
    cases extra <;> simp [PackingFieldDecodeMachine.decodedTapes,
      edgeTapes, vertexTapes, fieldTapes, regTape, slots, PackingMachineLayout.registers,
      baseTapes]

private theorem tally_exec (source : Extra) (destination : PackingSetupExpression.Input)
    (different : source ≠ .scanScratch) (base : Tape fixed K → List Bool)
    (n : Nat) (state : State)
    (sourceWord : base (.inr source) = List.replicate n true)
    (outputEmpty : base (regTape fixed K (input fixed K destination)) = [])
    (scratchEmpty : base (.inr .scanScratch) = []) :
    ∃ steps ≤ 3 * (n + 1) ^ 2 + 1,
      Exec (tallyToBinary fixed K source destination) ⟨state, base⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          Function.update (Function.update base (.inr source) [])
            (regTape fixed K (input fixed K destination)) n.bits⟩ := by
  have hSO : (Sum.inr source : Tape fixed K) ≠ regTape fixed K (input fixed K destination) := by
    simp [regTape, slots, PackingMachineLayout.registers]
  have hSC : (Sum.inr source : Tape fixed K) ≠ .inr .scanScratch := by simpa using different
  have hOC : regTape fixed K (input fixed K destination) ≠ Sum.inr Extra.scanScratch := by
    simp [regTape, slots, PackingMachineLayout.registers]
  have run := BinaryTallyMachine.plainTallyFromTapesInTime (.inr source)
    (regTape fixed K (input fixed K destination)) (.inr .scanScratch) hSO hSC hOC
    id none (BinaryTallyMachine.instruction (.inr source)
      (regTape fixed K (input fixed K destination)) (.inr .scanScratch) id none)
    (fun _ => rfl) base () n sourceWord outputEmpty scratchEmpty
  simpa only [tallyToBinary, arithmeticControl] using
    invokeExecInTime arithmeticControl (BinaryAddMachine.clean ()) .scan
      (BinaryTallyMachine.instruction (.inr source)
        (regTape fixed K (input fixed K destination)) (.inr .scanScratch) id none)
      ⟨state, base⟩ (BinaryAddMachine.clean ()) _ _ run

theorem parse_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (parsePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (parsePhases fixed K) ⟨state, initialTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), parsedTapes fixed K x⟩ := by
  have first := prepareGraph_exec (graphSlots fixed K) ⟨state, initialTapes fixed K x⟩ x
    (by rfl) (by rfl) (by rfl)
  rw [preparation_frame fixed K x] at first
  obtain ⟨a, ha, second⟩ := tally_exec fixed K .vertices .n (by decide)
    (fieldTapes fixed K x) x.graph.n (.graph (GraphFieldMachine.clean ()))
    rfl rfl rfl
  change Exec (tallyToBinary fixed K .vertices .n)
    ⟨.graph (GraphFieldMachine.clean ()), fieldTapes fixed K x⟩ a
    ⟨.arithmetic (BinaryAddMachine.clean ()), vertexTapes fixed K x⟩ at second
  obtain ⟨b, hb, third⟩ := tally_exec fixed K .edges .m (by decide)
    (vertexTapes fixed K x) x.graph.edges.length (.arithmetic (BinaryAddMachine.clean ()))
    (by simp [vertexTapes, fieldTapes, regTape, slots, PackingMachineLayout.registers])
    (by simp [vertexTapes, fieldTapes, regTape, slots, input,
      PackingMachineLayout.registers, PackingSetupMachine.input])
    (by simp [vertexTapes, fieldTapes, regTape, slots, PackingMachineLayout.registers])
  change Exec (tallyToBinary fixed K .edges .m)
    ⟨.arithmetic (BinaryAddMachine.clean ()), vertexTapes fixed K x⟩ b
    ⟨.arithmetic (BinaryAddMachine.clean ()), edgeTapes fixed K x⟩ at third
  have decoded := PackingFieldDecodeMachine.decodeNat_exec (thresholdSlots fixed K)
    (edgeTapes fixed K x) () x.k []
    (by simp [ edgeTapes, vertexTapes, fieldTapes, regTape, slots,
      PackingMachineLayout.registers])
    (by simp [ edgeTapes, vertexTapes, fieldTapes, regTape, slots,
      PackingMachineLayout.registers])
  rw [decoded_frame fixed K x] at decoded
  have fourth := PackingArithmeticProgram.exec _ _ _ _
    (.arithmetic (BinaryAddMachine.clean ())) decoded
  refine ⟨(1 + GraphPreparationMachine.steps x) + (a + (b + (1 + (2 * x.k.size + 2)))), ?_, ?_⟩
  · have hp := prepareGraph_cost x
    have hn := Nat.pow_le_pow_left (Nat.add_le_add_right (graph_vertexCount_le_bits x) 1) 2
    have hm := Nat.pow_le_pow_left (Nat.add_le_add_right (graph_edgeCount_le_bits x) 1) 2
    have hk : 2 * x.k.size + 2 ≤ (graphBits x).length + 1 := by
      rw [PackingFieldDecodeMachine.decodeNat_steps]
      simpa only [GraphFieldMachine.thresholdBits] using
        Nat.add_le_add_right (GraphFieldMachine.fieldBits_length_le .threshold x) 1
    simp only [parsePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    omega
  · exact PhaseRuns.cons first (PhaseRuns.cons second
      (PhaseRuns.cons third (PhaseRuns.single fourth)))

end

section

open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def powerPolynomial : Polynomial Nat :=
  80 * (Polynomial.X + 1) ^ 3 +
    2 * BinaryPowerMachine.timePolynomial.comp (2 * GraphPackingWidths.polynomial fixed K) + 4

private theorem tally_bound {n s : Nat} (h : n ≤ s) :
    BinaryToTallyMachine.runtimeBound n ≤ 40 * (s + 1) ^ 3 := by
  have size := (nat_size_le_self n).trans h
  calc
    BinaryToTallyMachine.runtimeBound n = 40 * (n + 1) * (n.size + 1) ^ 2 := rfl
    _ ≤ 40 * (s + 1) * (s + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 40 (by omega))
        (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by ring

theorem powerBudget_le (x : GraphReductionInput) :
    powerBudget fixed K x ≤ (powerPolynomial fixed K).eval (graphBits x).length := by
  let w := GraphPackingWidths.width fixed K x
  have ns : x.graph.n ≤ (graphBits x).length := graph_vertexCount_le_bits x
  have ms : x.graph.edges.length ≤ (graphBits x).length := graph_edgeCount_le_bits x
  have sw : (graphBits x).length + 1 ≤ w := GraphPackingWidths.input_length_le_width fixed K x
  have three : (3 : Nat).size ≤ w :=
    (nat_size_le_self 3).trans (GraphPackingWidths.small_constant_width fixed K x)
  have radix : (repetitions fixed K x + 1).size ≤ w :=
    (nat_size_le_self _).trans (GraphPackingWidths.repetitions_width fixed K x)
  have vertex := MachineComposition.natPolynomial_eval_mono BinaryPowerMachine.timePolynomial
    (show (3 : Nat).size + x.graph.n ≤ 2 * w by omega)
  have edge := MachineComposition.natPolynomial_eval_mono BinaryPowerMachine.timePolynomial
    (show (repetitions fixed K x + 1).size + x.graph.edges.length ≤ 2 * w by omega)
  have tn := tally_bound ns
  have tm := tally_bound ms
  simp only [powerPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_comp]
  change _ ≤ 80 * ((graphBits x).length + 1) ^ 3 +
    2 * BinaryPowerMachine.timePolynomial.eval (2 * w) + 4
  unfold powerBudget PackingPowerProgram.budget
  omega

def arithmeticPolynomial : Polynomial Nat :=
  PackingSetupMachine.timePolynomial (GraphPackingRegisters.parameters fixed K) +
    powerPolynomial fixed K + 1

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

variable (fixed : InventoryData) (K : Nat)

def timePolynomial : Polynomial Nat :=
  parsePolynomial fixed K + arithmeticPolynomial fixed K + finishPolynomial fixed K + 1

theorem prepare_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (timePolynomial fixed K).eval (graphBits x).length,
      Exec (prepare fixed K) ⟨state, initialTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), preparedTapes fixed K x⟩ := by
  obtain ⟨a, ha, arun⟩ := parse_exec fixed K x state
  obtain ⟨b, hb, brun⟩ := setup_exec fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨c, hc, crun⟩ := powers_exec fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨d, hd, drun⟩ := finish_exec fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  have middle := PhaseRuns.cons brun crun
  have whole := arun.append (middle.append drun)
  have actual := whole.toExec
  refine ⟨a + (b + c + d) + 1, ?_, ?_⟩
  · have powers := powerBudget_le fixed K x
    simp only [timePolynomial, arithmeticPolynomial, Polynomial.eval_add,
      Polynomial.eval_one] at ⊢
    omega
  · simpa only [prepare, parsePhases, powerPhases, List.cons_append, List.nil_append] using actual

end BinPackingGap.GraphPackingPreparation

end

end OAI
