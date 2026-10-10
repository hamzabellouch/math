import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchSuccess
import OAI.Combinatorics.ContingencyTables.Counting.CountingExecutedMachine
import OAI.Combinatorics.ContingencyTables.Counting.CountingPositiveWordLaw
import OAI.Combinatorics.ContingencyTables.Counting.ComputedCountingWords

namespace OAI

/-! # Confidence amplification preserves the executed source law -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem positive_sameLaw (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0<epsilon) (hd : 0<delta)
    (hs : SameLaw
      (fun bits : Fin (CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        TreeFraction.val (CountingPositiveProgram.output
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (ComputedCountingWords.root hEK r c b hne epsilon he)
        (ComputedCountingParameters.settings hEK r c b hne epsilon he))) :
    SameLaw (fun bits : Fin (positiveWidth (CountingDirectProgram.request r c b epsilon delta))→Bool =>
      TreeFraction.val (positive (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (ComputedCountingWords.estimate hEK r c b hne epsilon he delta) := by
  have hpos : 0<CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta) := by
    unfold CountingPositiveProgram.bitCount CountingDirectProgram.request
    rw [CountingPositiveProgram.phaseCount_data hEK r c b hne epsilon he]
    exact Nat.mul_pos (CountingPositiveProgram.phases_pos hEK r c b hne epsilon he)
      (CountingPositiveProgram.phaseWidth_pos _)
  have h := CountingAmplifiedProgram.sameLaw CountingPositiveProgram.output CountingPositiveProgram.bitCount
    (CountingDirectProgram.request r c b epsilon delta) hpos _ _ hs
  rw [CountingAmplifiedProgram.repeats_request r c b epsilon delta hd] at h
  exact h

theorem positive_success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta)
    (hp : 0<Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)))
    (hs : SameLaw
      (fun bits : Fin (CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        TreeFraction.val (CountingPositiveProgram.output
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
      (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (ComputedCountingWords.root hEK r c b hne epsilon he)
        (ComputedCountingParameters.settings hEK r c b hne epsilon he))) :
    1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Fin (positiveWidth (CountingDirectProgram.request r c b epsilon delta))→Bool =>
        if CountingBranchProgram.Accurate r c b epsilon (TreeFraction.val (positive
          (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits))) then (1:ℝ) else 0) := by
  have hl := positive_sameLaw hEK r c b hne epsilon delta he hd hs
  have ha := ComputedCountingWords.positive_success hEK hPL hCheeger r c b hne epsilon delta he he1 hd hp
  exact ha.trans_eq (hl (fun q => if CountingBranchProgram.Accurate r c b epsilon q then (1:ℝ) else 0)).symm

end
end ContingencyTables.CountingExecutedMachine

end OAI
