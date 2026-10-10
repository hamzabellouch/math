import OAI.Geometry.NodalSets.Charts.RadialMetricIdentification
import OAI.Geometry.NodalSets.Coefficients.WeightedCoefficientBounds
import OAI.Geometry.NodalSets.Elliptic.TargetWarpedComparison

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

lemma ambient_dot_self (v : AmbientBase) : (⇑v) ⬝ᵥ (⇑v) = ‖v‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, pow_two]

lemma original_coefficient_bounds
    (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    (a b r R rho : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hrho : r ≤ rho) (hR : rho ≤ R)
    (hlo : ∀ v : AmbientBase, a * ‖v‖^2 ≤ ambientMatrixForm A v v)
    (hhi : ∀ v : AmbientBase, ambientMatrixForm A v v ≤ b * ‖v‖^2) :
    (∀ v : AmbientBase, (r/b) * ‖v‖^2 ≤ ambientMatrixForm (weightedBaseMatrix A rho) v v ∧
      ambientMatrixForm (weightedBaseMatrix A rho) v v ≤ (R/a) * ‖v‖^2) ∧
    a^5/R^2 ≤ (ambientCircleWeight A rho)^2 ∧
      (ambientCircleWeight A rho)^2 ≤ b^5/r^2 := by
  have hl (v : Fin 5 → ℝ) : a * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
    simpa [ambientMatrixForm_dot, ← ambient_dot_self] using hlo (WithLp.toLp 2 v)
  have hh (v : Fin 5 → ℝ) : v ⬝ᵥ (A *ᵥ v) ≤ b * (v ⬝ᵥ v) := by
    simpa [ambientMatrixForm_dot, ← ambient_dot_self] using hhi (WithLp.toLp 2 v)
  refine ⟨?_, ?_⟩
  · intro v
    simpa [ambientMatrixForm_dot, ambient_dot_self] using
      weightedBaseMatrix_bounds A hA a b r R rho ha hb hr hrho hR hl hh ⇑v
  · simpa [ambientCircleWeight] using
      determinant_density_bounds A hA a b r R rho ha hb hr hrho hR hl hh

lemma coefficient_comparison_constants_pos (a b r R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hR : 0 < R) :
    0 < min (r/b) (a^5/R^2) ∧ 0 < max (R/a) (b^5/r^2) := by
  constructor
  · exact lt_min (div_pos hr hb) (div_pos (pow_pos ha _) (sq_pos_of_pos hR))
  · exact lt_max_of_lt_left (div_pos hR ha)

lemma independentAmbientMetric_original_comparison
    (a b r R : ℝ) (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r)
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hlo : ∀ x v, a * ‖v‖^2 ≤ ambientMatrixForm (A x) v v)
    (hhi : ∀ x v, ambientMatrixForm (A x) v v ≤ b * ‖v‖^2)
    (hrho : ∀ x, r ≤ rho x) (hR : ∀ x, rho x ≤ R)
    (x : Manifold5) (v : TangentSpace modelWithCorners x) :
    min (r/b) (a^5/R^2) * roundProductMetric.inner x v v ≤
      (independentAmbientMetric A rho hA hp hr hrp).inner x v v ∧
    (independentAmbientMetric A rho hA hp hr hrp).inner x v v ≤
      max (R/a) (b^5/r^2) * roundProductMetric.inner x v v := by
  have h (y : Base) := original_coefficient_bounds (A y) (hp y) a b r R (rho y)
    ha hb hr0 (hrho y) (hR y) (hlo y) (hhi y)
  apply ambientWeightedMetric_comparison
  · intro y w
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖w‖)).trans ((h y).1 w).1
  · intro y w
    exact ((h y).1 w).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ‖w‖))
  · intro y
    exact (min_le_right _ _).trans (h y).2.1
  · intro y
    exact (h y).2.2.trans (le_max_right _ _)

end
end Yau.Target

end OAI
