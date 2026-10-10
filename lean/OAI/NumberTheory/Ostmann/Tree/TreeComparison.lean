import OAI.NumberTheory.Ostmann.Tree.QuarterPowerBound
import OAI.NumberTheory.Ostmann.Tree.TreeComparisonSquared

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

def treeComparisonConstant (k : ℕ) : ℝ := 2*Real.sqrt (treeComparisonSquaredConstant k)

theorem treeComparisonConstant_nonneg (k : ℕ) : 0≤treeComparisonConstant k := by
  unfold treeComparisonConstant
  positivity

theorem treeComparisonConstant_pos (k : ℕ) : 0<treeComparisonConstant k := by
  unfold treeComparisonConstant treeComparisonSquaredConstant treeProjectionConstant
  positivity

theorem tree_comparison {k b : ℕ} (P Q : LeafPartition (k+2) b)
    (T1 T2 : Diagram (ZMod p) (k+2)) (hp : 3≤p) (hb : 4*b≤3*2^(k+2))
    (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    ‖diagramCorrelation P Q T1 T2 g‖≤
      treeComparisonConstant k*((correlationBound g:ℝ)+(p:ℝ)^(-(1/4:ℝ))) := by
  exact squared_error_to_quarter_bound _ _ _ _ (norm_nonneg _) (by positivity)
    (treeComparisonSquaredConstant_nonneg k)
    (by exact_mod_cast (Fact.out : p.Prime).pos)
    (tree_comparison_sq P Q T1 T2 hp hb g hg0 hg)

theorem tree_comparison_of_two_le {d b : ℕ} (P Q : LeafPartition d b)
    (T1 T2 : Diagram (ZMod p) d) (hp : 3≤p) (hd : 2≤d) (hb : 4*b≤3*2^d)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    ‖diagramCorrelation P Q T1 T2 g‖≤
      treeComparisonConstant (d-2)*((correlationBound g:ℝ)+(p:ℝ)^(-(1/4:ℝ))) := by
  obtain ⟨k,rfl⟩ : ∃ k,d=k+2 := ⟨d-2,(Nat.sub_add_cancel hd).symm⟩
  simpa only [Nat.add_sub_cancel] using tree_comparison P Q T1 T2 hp hb g hg0 hg

end
end Ostmann.Tree

end OAI
