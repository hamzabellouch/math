import OAI.Combinatorics.ContingencyTables.Sampling.SmallCoordinateSums
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalOriginalResiduals

namespace OAI

/-! # Actual padded residual margins change by at most two on exchange edges -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextFibres IntegerWeightedTransport

lemma nat_residual_difference (r P A B : ℕ) (hA : A ≤ r) (hB : B ≤ r) :
    |((r-A+P:ℕ):ℤ)-((r-B+P:ℕ):ℤ)|=|(A:ℤ)-B| := by
  rw [Nat.cast_add,Nat.cast_add,Nat.cast_sub hA,Nat.cast_sub hB]
  have he : (r:ℤ)-A+P-((r:ℤ)-B+P) = -((A:ℤ)-B) := by ring
  rw [he,abs_neg]

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma exchange_residual_margins (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (x y : PhysicalStates small B r c L)
    (hxcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L x k) ≤ B i j)
    (hycap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L y k) ≤ B i j)
    (hxy : IntegerExchangeAdjacent (physicalProfile small B r c L x) (physicalProfile small B r c L y)) :
    (∀ i,|(residualRows small B r c L y i:ℤ)-residualRows small B r c L x i| ≤ 2) ∧
    (∀ j,|(residualColumns small B r c L y j:ℤ)-residualColumns small B r c L x j| ≤ 2) := by
  have hx := physical_original_residuals small B r c L x hxcap
  have hy := physical_original_residuals small B r c L y hycap
  constructor
  · intro i
    unfold residualRows
    rw [nat_residual_difference _ _ _ _ (hy.1 i) (hx.1 i)]
    exact exchange_smallRow_abs small _ _ hxy i
  · intro j
    unfold residualColumns
    rw [nat_residual_difference _ _ _ _ (hy.2 j) (hx.2 j)]
    exact exchange_smallColumn_abs small B _ _ (naturalProfile_bounded x.val.val)
      (naturalProfile_bounded y.val.val) hxy j

end ContingencyTables.SmallGraphProfiles

end OAI
