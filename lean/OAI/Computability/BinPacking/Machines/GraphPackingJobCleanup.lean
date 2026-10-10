import OAI.Computability.BinPacking.Machines.GraphPackingPreparationFinish

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)

variable (fixed : InventoryData) (K : Nat)

def cleanupPhases : List (GraphPackingProgram.Program fixed K) :=
  [GraphPackingProgram.incrementEdge fixed K,
    GraphPackingProgram.setWork fixed K .leftEndpoint 0,
    GraphPackingProgram.setWork fixed K .rightEndpoint 0,
    GraphPackingProgram.setWork fixed K .leftPower 0,
    GraphPackingProgram.setWork fixed K .rightPower 0,
    GraphPackingProgram.setItem fixed K .labelPower 0,
    GraphPackingProgram.setItem fixed K .repetitionOne 0]

private def cleanupWidthTimePolynomial : Polynomial Nat :=
  64 * (2 * Polynomial.X + 1) ^ 2 +
    PackingLayoutCommands.setOtherTime (Numerator fixed) denominator
      (Other := Other fixed K) (.inr .leftEndpoint) 0 +
    PackingLayoutCommands.setOtherTime (Numerator fixed) denominator
      (Other := Other fixed K) (.inr .rightEndpoint) 0 +
    PackingLayoutCommands.setOtherTime (Numerator fixed) denominator
      (Other := Other fixed K) (.inr .leftPower) 0 +
    PackingLayoutCommands.setOtherTime (Numerator fixed) denominator
      (Other := Other fixed K) (.inr .rightPower) 0 +
    PackingLayoutCommands.setInputTime (Numerator fixed) denominator
      (Other := Other fixed K) .labelPower 0 +
    PackingLayoutCommands.setInputTime (Numerator fixed) denominator
      (Other := Other fixed K) .repetitionOne 0

def cleanupTimePolynomial : Polynomial Nat :=
  (cleanupWidthTimePolynomial fixed K).comp (GraphPackingWidths.polynomial fixed K)

theorem cleanup_exec (x : GraphReductionInput) (e : x.graph.Edge)
    (base : Tape fixed K → List Bool) (state : State) :
    ∃ steps ≤ (cleanupTimePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (cleanupPhases fixed K)
        ⟨state, tapes (Numerator fixed) denominator base
          (completedInputs fixed K x e.val (x.graph.right e).val)
          (loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator base (inputs fixed K x (e.val + 1))
            (preparedOther fixed K x)⟩ := by
  let width := GraphPackingWidths.width fixed K x
  let initialInput := completedInputs fixed K x e.val (x.graph.right e).val
  let initialOther := loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val
  let nextPower := (GraphPackingPreparation.repetitions fixed K x + 1) ^ (e.val + 1)
  let advancedInput := Function.update initialInput .edgePower nextPower
  let other₁ := Function.update initialOther (.inr Work.leftEndpoint) 0
  let other₂ := Function.update other₁ (.inr Work.rightEndpoint) 0
  let other₃ := Function.update other₂ (.inr Work.leftPower) 0
  let other₄ := Function.update other₃ (.inr Work.rightPower) 0
  let input₁ := Function.update advancedInput .labelPower 0
  let input₂ := Function.update input₁ .repetitionOne 0
  let clean : State := .arithmetic (BinaryAddMachine.clean ())
  have initialInputWidth : ∀ a, (initialInput a).size ≤ width :=
    completedInputs_width fixed K x e.val (x.graph.right e).val
      (Nat.le_of_lt e.isLt) (x.graph.right e).isLt
  have initialOtherWidth : ∀ r, (initialOther r).size ≤ width :=
    loadedOther_width fixed K x (x.graph.left e).val (x.graph.right e).val
      (x.graph.left e).isLt (x.graph.right e).isLt
  have zeroWidth : (0 : Nat).size ≤ width := by simp
  have advancedInputWidth : ∀ a, (advancedInput a).size ≤ width :=
    GraphPackingWidths.update_width fixed K x initialInput initialInputWidth .edgePower
      nextPower (GraphPackingWidths.edge_power_width fixed K x (e.val + 1)
        (Nat.succ_le_of_lt e.isLt))
  have other₁Width : ∀ r, (other₁ r).size ≤ width :=
    GraphPackingWidths.update_width fixed K x initialOther initialOtherWidth _ 0 zeroWidth
  have other₂Width : ∀ r, (other₂ r).size ≤ width :=
    GraphPackingWidths.update_width fixed K x other₁ other₁Width _ 0 zeroWidth
  have other₃Width : ∀ r, (other₃ r).size ≤ width :=
    GraphPackingWidths.update_width fixed K x other₂ other₂Width _ 0 zeroWidth
  have other₄Width : ∀ r, (other₄ r).size ≤ width :=
    GraphPackingWidths.update_width fixed K x other₃ other₃Width _ 0 zeroWidth
  have input₁Width : ∀ a, (input₁ a).size ≤ width :=
    GraphPackingWidths.update_width fixed K x advancedInput advancedInputWidth _ 0 zeroWidth
  have temporaryZero : initialOther (.inr Work.temporary) = 0 :=
    loaded_helper_zero fixed K x (x.graph.left e).val (x.graph.right e).val
      .temporary (Or.inr (Or.inr (Or.inl rfl)))
  have baseValue : initialOther (GraphPackingProgram.otherSetup fixed K .base) =
      GraphPackingPreparation.repetitions fixed K x + 1 := by
    change loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val
      (.inl (PackingSetupMachine.output (parameters fixed K) .base)) = _
    rw [loaded_setup]
    rfl
  have edgeValue : initialInput .edgePower =
      (GraphPackingPreparation.repetitions fixed K x + 1) ^ e.val := by
    simp [initialInput, completedInputs, inputs]
  have productValue : PackingRegisterUpdate.operation .multiply
      (initialOther (GraphPackingProgram.otherSetup fixed K .base))
      (initialInput .edgePower) = nextPower := by
    simp only [PackingRegisterUpdate.operation, baseValue, edgeValue]
    exact (Nat.mul_comm _ _).trans (Nat.pow_succ _ _).symm
  obtain ⟨n₀, b₀, r₀⟩ := PackingVertexUpdate.general_exec
    (Numerator fixed) denominator .edgePower
    (GraphPackingProgram.otherSetup fixed K .base) (.inr Work.temporary)
    (by simp [GraphPackingProgram.otherSetup]) .multiply
    base initialInput initialOther temporaryZero state
  rw [productValue] at r₀
  change Exec (GraphPackingProgram.incrementEdge fixed K)
    ⟨state, tapes (Numerator fixed) denominator base initialInput initialOther⟩ n₀
    ⟨clean, tapes (Numerator fixed) denominator base advancedInput initialOther⟩ at r₀
  have multiplicationBound : n₀ ≤ 64 * (2 * width + 1) ^ 2 := by
    apply b₀.trans
    apply Nat.mul_le_mul_left 64
    apply Nat.pow_le_pow_left
    have hb := initialOtherWidth (GraphPackingProgram.otherSetup fixed K .base)
    have he := initialInputWidth .edgePower
    omega
  obtain ⟨n₁, b₁, r₁⟩ := PackingLayoutCommands.setOther_exec
    (Numerator fixed) denominator (.inr Work.leftEndpoint) 0
    base advancedInput initialOther clean width advancedInputWidth initialOtherWidth
  obtain ⟨n₂, b₂, r₂⟩ := PackingLayoutCommands.setOther_exec
    (Numerator fixed) denominator (.inr Work.rightEndpoint) 0
    base advancedInput other₁ clean width advancedInputWidth other₁Width
  obtain ⟨n₃, b₃, r₃⟩ := PackingLayoutCommands.setOther_exec
    (Numerator fixed) denominator (.inr Work.leftPower) 0
    base advancedInput other₂ clean width advancedInputWidth other₂Width
  obtain ⟨n₄, b₄, r₄⟩ := PackingLayoutCommands.setOther_exec
    (Numerator fixed) denominator (.inr Work.rightPower) 0
    base advancedInput other₃ clean width advancedInputWidth other₃Width
  obtain ⟨n₅, b₅, r₅⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .labelPower 0
    base advancedInput other₄ clean width advancedInputWidth other₄Width
  obtain ⟨n₆, b₆, r₆⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 0
    base input₁ other₄ clean width input₁Width other₄Width
  have finalOther : other₄ = preparedOther fixed K x :=
    clearedOther_eq fixed K x (x.graph.left e).val (x.graph.right e).val
  have finalInput : input₂ = inputs fixed K x (e.val + 1) :=
    clearedInputs_eq fixed K x e.val (x.graph.right e).val
  have runs := PhaseRuns.cons r₀ (PhaseRuns.cons r₁ (PhaseRuns.cons r₂
    (PhaseRuns.cons r₃ (PhaseRuns.cons r₄ (PhaseRuns.cons r₅ (PhaseRuns.single r₆))))))
  refine ⟨n₀ + (n₁ + (n₂ + (n₃ + (n₄ + (n₅ + n₆))))), ?_, ?_⟩
  · rw [cleanupTimePolynomial, Polynomial.eval_comp]
    change _ ≤ (cleanupWidthTimePolynomial fixed K).eval width
    simp only [cleanupWidthTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
    omega
  · change PhaseRuns (cleanupPhases fixed K)
      ⟨state, tapes (Numerator fixed) denominator base initialInput initialOther⟩ _
      ⟨clean, tapes (Numerator fixed) denominator base
        (inputs fixed K x (e.val + 1)) (preparedOther fixed K x)⟩
    rw [← finalOther, ← finalInput]
    simpa only [cleanupPhases, GraphPackingProgram.setWork, GraphPackingProgram.setItem]
      using runs

end BinPackingGap.GraphPackingJobs

end

end OAI
