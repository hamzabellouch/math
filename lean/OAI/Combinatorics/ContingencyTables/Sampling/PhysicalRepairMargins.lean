import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalExchangeMargins
import OAI.Combinatorics.ContingencyTables.Sampling.RepairSmallMargins

namespace OAI

/-! # The physical padded residuals change by at most one on a repair -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextFibres SmallContextCoordinates

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma repair_residual_margins (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (x y : PhysicalStates small B r c L)
    (hxcap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L x k) ≤ B i j)
    (hycap : ∀ i j,small i j=false → (∑ k,residualRows small B r c L y k) ≤ B i j)
    (s t : I×J)
    (hd : IsDefect (smallView small (physicalProfile small B r c L x) false)
      (smallQ small B (physicalProfile small B r c L x)) s t)
    (ht : small t.1 t.2=true)
    (hcap : ∀ a : Cells small,repairMatrix
      (smallView small (physicalProfile small B r c L x) false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (heq : physicalProfile small B r c L y=repairedProfile small B (physicalProfile small B r c L x) s t) :
    (∀ i,|(residualRows small B r c L y i:ℤ)-residualRows small B r c L x i| ≤ 1) ∧
    (∀ j,|(residualColumns small B r c L y j:ℤ)-residualColumns small B r c L x j| ≤ 1) := by
  have hx := physical_original_residuals small B r c L x hxcap
  have hy := physical_original_residuals small B r c L y hycap
  have hm := repair_small_margin_abs small B (physicalProfile small B r c L x) s t hd ht hcap
  constructor
  · intro i
    unfold residualRows
    rw [nat_residual_difference _ _ _ _ (hy.1 i) (hx.1 i),heq]
    exact hm.1 i
  · intro j
    unfold residualColumns
    rw [nat_residual_difference _ _ _ _ (hy.2 j) (hx.2 j),heq]
    exact hm.2 j

end ContingencyTables.SmallGraphProfiles

end OAI
