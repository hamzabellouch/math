import OAI.Analysis.Pureness.Stabilization.MatrixLimit
import OAI.Analysis.Pureness.Stabilization.CuntzFunctor
import OAI.Analysis.Pureness.Stabilization.Perturbation

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance : PartialOrder (MatrixLimit A) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (MatrixLimit A) := CStarAlgebra.spectralOrderedRing _

theorem matrixLimit_positive_approximation (a : Positive (MatrixLimit A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (M : Positive (FinMatrix A n)),
      ‖a.1-(Positive.map (matrixLimitStage n) M).1‖ < ε := by
  have hc : Continuous (fun x : MatrixLimit A => star x*x) := continuous_star.mul continuous_id
  obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := CFC.sqrt a.1)) ε hε
  obtain ⟨n,M,hM⟩ := matrixLimit_finite_approximation (CFC.sqrt a.1) hδ
  refine ⟨n,Positive.starMul M,?_⟩
  have hd : dist (matrixLimitStage n M) (CFC.sqrt a.1) < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hM
  have he : star (CFC.sqrt a.1)*CFC.sqrt a.1 = a.1 := by
    rw [(CFC.sqrt_nonneg a.1).star_eq, CFC.sqrt_mul_sqrt_self a.1 a.2]
  have hh := h hd
  rw [he, dist_eq_norm, norm_sub_rev] at hh
  simpa only [Positive.map, Positive.starMul, map_mul, map_star] using hh

theorem matrixLimit_cut_below_finite (a : Positive (MatrixLimit A)) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ (n : ℕ) (M : Positive (FinMatrix A n)),
      CuntzBelow (Positive.cut ε a) (Positive.map (matrixLimitStage n) M) := by
  obtain ⟨n,M,hM⟩ := matrixLimit_positive_approximation a (show (0 : ℝ) < ε from hε)
  exact ⟨n,M,cut_cuntzBelow_of_norm_sub_lt a _ ε hε hM⟩
end CuntzTrace

end

end OAI
