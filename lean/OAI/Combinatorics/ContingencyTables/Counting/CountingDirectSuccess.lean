import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectLaw

namespace OAI

/-! # Accuracy of the executed direct counting branch -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication GridBoundary CommonBasesFPRAS
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem success (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (hzero : Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he))=0) :
    1-(delta:ℝ) ≤ uniformAverage
      (fun bits : Fin (budget (request r c b epsilon delta))→Bool =>
        if (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ) ≤
            (TreeFraction.val (output (request r c b epsilon delta,List.ofFn bits)):ℝ) ∧
          (TreeFraction.val (output (request r c b epsilon delta,List.ofFn bits)):ℝ) ≤
            (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
        then (1:ℝ) else 0) := by
  let event := fun q : ℚ => if
    (1-(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ) ≤ (q:ℝ) ∧
      (q:ℝ) ≤ (1+(epsilon:ℝ))*(Fintype.card (BoundedTable r c b):ℝ)
    then (1:ℝ) else 0
  have hs := ComputedCountingZero.zero_success hEK hPL hCheeger r c b hne
    epsilon delta he he1 hd hzero
  exact hs.trans_eq (sameLaw hEK r c b hne epsilon delta he hd event).symm

end
end ContingencyTables.CountingDirectProgram

end OAI
