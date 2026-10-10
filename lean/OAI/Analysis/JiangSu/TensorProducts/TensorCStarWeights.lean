import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights
import OAI.Analysis.JiangSu.CStarAlgebras.CStarNormCompletion
import OAI.Analysis.JiangSu.CentralSequences.CStarCentralWeights

namespace OAI

section

noncomputable section
namespace Pureness.CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
variable {ι : Type*} [Fintype ι]
lemma central_weighted_bound (q : CStarAlgebraNorm R) (v y : ι → R) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ i, IsSelfAdjoint (v i)) (hc : ∀ i, Commute (v i) (y i))
    (hp : q.toAlgebraNorm (∑ i,v i*v i) ≤ 1) (hy : ∀ i,q.toAlgebraNorm (y i) ≤ C) :
    q.toAlgebraNorm (∑ i,(v i*v i)*y i) ≤ C := by
  let : PartialOrder q.Completion := CStarAlgebra.spectralOrder q.Completion
  let : StarOrderedRing q.Completion := CStarAlgebra.spectralOrderedRing q.Completion
  rw [←q.completionMap_norm,map_sum]
  simp only [map_mul]
  apply CStarCentralWeights.central_weighted_sum_bound _ _ hC
  · intro i
    exact (hv i).map q.completionMap
  · intro i
    exact (hc i).map q.completionMap
  · simpa only [←map_mul, ←map_sum, q.completionMap_norm] using hp
  · simpa only [q.completionMap_norm] using hy
end Pureness.CStarAlgebraNorm

end
end

end OAI
