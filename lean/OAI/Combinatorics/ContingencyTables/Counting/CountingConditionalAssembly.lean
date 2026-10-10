import OAI.Combinatorics.ContingencyTables.Counting.CountingAmplifiedSourceLaw
import OAI.Combinatorics.ContingencyTables.Counting.CountingPublicAccuracy

namespace OAI

/-! # Assembly of the public counting specification from its executed history law -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS CommonBasesFPRAS CompanionFactorialApplication GridBoundary FiniteObservableTransport
open scoped Classical
noncomputable section

theorem statement_of_single_law
    (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger (Grid (I := Fin q) k))
    (hlaw : ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
      (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0<epsilon),
      SameLaw
        (fun bits : Fin (CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta))→Bool =>
          TreeFraction.val (CountingPositiveProgram.output
            (CountingDirectProgram.request r c b epsilon delta,List.ofFn bits)))
        (RootedCountingWords.flatEstimate (ComputedCountingParameters.data hEK r c b hne epsilon he)
          (ComputedCountingWords.root hEK r c b hne epsilon he)
          (ComputedCountingParameters.settings hEK r c b hne epsilon he))) :
    Algorithms.CountingStatement := by
  obtain ⟨C,d,hC,ht⟩ := public_time hEK
  refine ⟨machine,C,d,hC,?_⟩
  intro m n _ _ r c b _ epsilon delta he he1 hd _
  have htime := ht m n r c b epsilon delta he hd
  refine ⟨outputs_nonnegative r c b epsilon delta _ htime,
    (fun hz => outputs_zero hEK r c b epsilon delta hz _ htime),?_⟩
  apply public_success hEK hPL hCheeger r c b epsilon delta he he1 hd
  · intro hne hp
    exact positive_success hEK hPL hCheeger r c b hne epsilon delta he he1 hd hp
      (hlaw m n r c b hne epsilon delta he)
  · exact htime

end
end ContingencyTables.CountingExecutedMachine

end OAI
