import OAI.Combinatorics.ContingencyTables.Counting.CountingExecutedMachine
import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchSuccess
import OAI.Combinatorics.ContingencyTables.Counting.CountingMachineMainEvent

namespace OAI

/-! # Transporting the concrete counting accuracy event to public machine tapes -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS MatchingFPRAS.PhysicalStream CommonBasesFPRAS CompanionFactorialApplication GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma accurate_iff (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon q : ℚ) :
    ((1-epsilon)*(Algorithms.count r c b:ℚ)≤q ∧
      q≤(1+epsilon)*(Algorithms.count r c b:ℚ)) ↔
      CountingBranchProgram.Accurate r c b epsilon q := by
  unfold CountingBranchProgram.Accurate Algorithms.count
  constructor <;> rintro ⟨hl,hu⟩ <;> constructor
  · exact_mod_cast hl
  · exact_mod_cast hu
  · exact_mod_cast hl
  · exact_mod_cast hu

attribute [local irreducible] CountingPositiveProgram.output CountingAmplifiedProgram.output
  CountingBranchProgram.output CountingBranchProgram.publicOutput CountingBranchProgram.machine
  CountingExecutedMachine.machine

theorem public_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hpositive : ∀ hne : ∃ X,TableTightening.Feasible r c b X,
      0<Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) →
      1-(delta:ℝ) ≤ uniformAverage
        (fun bits : Fin (positiveWidth (CountingDirectProgram.request r c b epsilon delta))→Bool =>
          if CountingBranchProgram.Accurate r c b epsilon (TreeFraction.val (positive
            (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0))
    (t : ℕ) (ht : machineTime (Algorithms.encodeCountingInput r c b epsilon delta)≤t) :
    1-delta ≤ ((Algorithms.goodCountingTapes machine r c b epsilon delta t).card:ℚ)/(2:ℚ)^t := by
  let P := fun q : ℚ => (1-epsilon)*(Algorithms.count r c b:ℚ)≤q ∧
    q≤(1+epsilon)*(Algorithms.count r c b:ℚ)
  have hraw := CountingBranchProgram.success hEK hPL hCheeger positive positiveWidth
    r c b epsilon delta he he1 hd hpositive
  have hs : 1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Bits (wordCount (Algorithms.encodeCountingInput r c b epsilon delta)) =>
        if P (sourceValue (Algorithms.encodeCountingInput r c b epsilon delta) bits) then (1:ℝ) else 0) := by
    simp only [P,accurate_iff,sourceValue,CountingBranchProgram.sourceValue,
      CountingBranchProgram.parsedInput_public]
    unfold wordCount CountingBranchProgram.publicBudget
    rw [CountingInputParser.public_spec]
    exact hraw
  rw [show machine=FiniteWordExecution.machine
    (CountingBranchProgram.publicBudgetRealizer positiveWidth positiveWidthRealizer)
    (CountingBranchProgram.publicOutputRealizer positive positiveRealizer) from by
      unfold machine CountingBranchProgram.machine; rfl]
  exact CountingMachineEvents.goodTapes_success
    (CountingBranchProgram.publicBudgetRealizer positiveWidth positiveWidthRealizer)
    (CountingBranchProgram.publicOutputRealizer positive positiveRealizer)
    r c b epsilon delta
    (fun bs a ha => (CountingBranchProgram.publicOutput_symbols positive _ a ha).2)
    (sourceValue (Algorithms.encodeCountingInput r c b epsilon delta))
    (CountingBranchProgram.sourceValue_output positive positiveWidth _)
    hs t ht

end
end ContingencyTables.CountingExecutedMachine

end OAI
