import OAI.NumberTheory.Ostmann.Tree.TreeFiberMajorization

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Ostmann.FiniteField QuartetFactorization Density
variable {p : ℕ} [Fact p.Prime] {k b : ℕ}

theorem treeProjection_l2_bound (P : LeafPartition (k+2) b)
    (c : BalancedSelection P.label (quartetCut k).label)
    (T : Diagram (ZMod p) (k+2)) (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    Density.average (fun M => ‖c.projection (T.value g) M‖^2)≤
      treeProjectionConstant k*treeError g := by
  have hd := horizontal_fiber_bound (bottomCut k) T
    (fun M => ‖c.projection (T.value g) M‖^2) (treeMajorant P c T g)
    (treeMajorant_nonneg P c T g) (treeProjection_fiber_bound P c T g hg0)
  apply hd.trans
  calc
    _ ≤ ((2^(2^k-1):ℕ):ℝ)*((25600*treeError g)*(256:ℝ)^(2^k)) :=
      mul_le_mul_of_nonneg_left (treeMajorant_mean P c T g hg0 hg) (by positivity)
    _ = _ := by unfold treeProjectionConstant; ring

end
end Ostmann.Tree

end OAI
