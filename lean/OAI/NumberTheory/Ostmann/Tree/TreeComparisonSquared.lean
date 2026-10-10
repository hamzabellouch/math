import OAI.NumberTheory.Ostmann.Tree.CoupledDiagramCorrelation
import OAI.NumberTheory.Ostmann.Tree.DensityL2
import OAI.NumberTheory.Ostmann.Tree.TreeProjectionBound

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators ComplexConjugate
open Ostmann.FiniteField Ostmann.Arithmetic.ResidueHaar
variable {p : ℕ} [Fact p.Prime]

def treeComparisonSquaredConstant (k : ℕ) : ℝ :=
  treeProjectionConstant k*(3:ℝ)^(2^(k+2))

theorem treeComparisonSquaredConstant_nonneg (k : ℕ) : 0≤treeComparisonSquaredConstant k :=
  mul_nonneg (treeProjectionConstant_nonneg k) (by positivity)

theorem tree_comparison_sq {k b : ℕ} (P Q : LeafPartition (k+2) b)
    (T1 T2 : Diagram (ZMod p) (k+2)) (hp : 3≤p) (hb : 4*b≤3*2^(k+2))
    (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    ‖diagramCorrelation P Q T1 T2 g‖^2≤treeComparisonSquaredConstant k*treeError g := by
  classical
  obtain ⟨c⟩ := exists_quartet_cycle P hb
  have hc := diagramCorrelation_projection_sq P Q c T1 T2 g
  have h1 := treeProjection_l2_bound P c T1 g hg0 hg
  have h2 := Density.diagram_l2_bound T2 hp g hg
  simp only [real_average_fintype_congr _
    (inferInstance : Fintype (Leaves (k+2) → (ZMod p)ˣ))] at hc h1 h2
  apply hc.trans
  calc
    _ ≤ (treeProjectionConstant k*treeError g)*(3:ℝ)^(2^(k+2)) :=
      mul_le_mul h1 h2
        (mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
        (mul_nonneg (treeProjectionConstant_nonneg k) (treeError_nonneg g))
    _ = _ := by unfold treeComparisonSquaredConstant; ring

end
end Ostmann.Tree

end OAI
