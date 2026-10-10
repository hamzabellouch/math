import OAI.NumberTheory.Ostmann.Arithmetic.PermutationDiagramComparisonUniversal
import OAI.NumberTheory.Ostmann.Conclusion.LowLevelBadPairs

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PermutationDiagramComparison
open Ostmann.FiniteField
variable {p depth m : ℕ} [Fact p.Prime]

theorem slotCorrelation_transfer_good_bound (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (hm : 0 < m) (T1 T2 : Tree.Diagram (ZMod p) depth) (hp : 3≤p)
    (hgood : ¬Conclusion.TransferBadArrangement σ)
    (g : ZMod p → ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    ‖slotCorrelation σ T1 T2 g‖≤Tree.treeComparisonConstant (depth-2)*
      ((correlationBound g:ℝ)+(p:ℝ)^(-(1/4:ℝ))) := by
  have hh : ¬(2^depth≤2) ∧ ¬Conclusion.BadArrangement σ := not_or.mp hgood
  have hd : 2≤depth := by
    by_contra h
    have he : depth=0 ∨ depth=1 := by omega
    rcases he with rfl | rfl <;> norm_num at hh
  apply slotCorrelation_good_bound σ hm T1 T2 hp hd
  · exact Nat.le_of_not_gt hh.2
  · exact hg0
  · exact hg

end Ostmann.Arithmetic.PermutationDiagramComparison

end

end OAI
