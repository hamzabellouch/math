import OAI.NumberTheory.Ostmann.Arithmetic.PermutationDiagramComparisonProducts
import OAI.NumberTheory.Ostmann.Tree.TreeComparison

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PermutationDiagramComparison
open scoped BigOperators ComplexConjugate
open Ostmann.FiniteField
open ResidueHaar
variable {p depth m : ℕ} [Fact p.Prime]

def slotCorrelation (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (T1 T2 : Tree.Diagram (ZMod p) depth) (g : ZMod p → ℂ) : ℂ :=
  average (fun samples : Fin (2^depth) × Fin m → (ZMod p)ˣ =>
    T1.value g (slotLeaves σ samples).1 * conj (T2.value g (slotLeaves σ samples).2))

theorem slotCorrelation_eq_diagramCorrelation (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (hm : 0 < m) (T1 T2 : Tree.Diagram (ZMod p) depth) (g : ZMod p → ℂ) :
    slotCorrelation σ T1 T2 g = Tree.diagramCorrelation
      (TreePermutationHaar.leftPartition σ) (TreePermutationHaar.rightPartition σ hm) T1 T2 g := by
  have hh := TreePermutationHaar.tree_products_uniform (F:=ZMod p) σ hm
    (fun x => T1.value g x.val.1 * conj (T2.value g x.val.2))
  change average (fun samples =>
    T1.value g (TreePermutationHaar.leafPairEquiv (PermutationHaar.products σ samples)).1 *
      conj (T2.value g (TreePermutationHaar.leafPairEquiv (PermutationHaar.products σ samples)).2)) = _ at hh
  simp only [←slotLeaves_eq_leafPairEquiv] at hh
  exact hh

theorem slotCorrelation_good_bound (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (hm : 0 < m) (T1 T2 : Tree.Diagram (ZMod p) depth) (hp : 3≤p) (hd : 2≤depth)
    (hgood : 4*TreePermutationHaar.blocks σ≤3*2^depth)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    ‖slotCorrelation σ T1 T2 g‖≤Tree.treeComparisonConstant (depth-2)*
      ((correlationBound g:ℝ)+(p:ℝ)^(-(1/4:ℝ))) := by
  rw [slotCorrelation_eq_diagramCorrelation σ hm]
  exact Tree.tree_comparison_of_two_le _ _ T1 T2 hp hd hgood g hg0 hg

end Ostmann.Arithmetic.PermutationDiagramComparison

end

end OAI
