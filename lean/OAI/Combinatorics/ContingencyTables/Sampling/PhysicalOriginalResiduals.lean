import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalResidualMargins

namespace OAI

/-! # Positive completion weight enforces the original residual tests -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physical_original_residuals (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L)
    (hcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j) :
    OriginalResidualsNonnegative small B
      (smallView small (physicalProfile small B r c L z) false)
      (smallView small (physicalProfile small B r c L z) true) r c := by
  have hh := hardMarginal_eq_completionCount small B r c L
    (physicalProfile small B r c L z) (naturalProfile_bounded z.val.val) hcap
  by_contra hn
  rw [ite_eq_right hn] at hh
  have hp := z.property
  change 0 < hardMarginal small B r c L (physicalProfile small B r c L z) at hp
  rw [hh] at hp
  exact lt_irrefl _ hp

end ContingencyTables.SmallGraphProfiles

end OAI
