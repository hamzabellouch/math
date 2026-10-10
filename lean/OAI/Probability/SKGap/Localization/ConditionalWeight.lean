import Mathlib
import OAI.Probability.SKGap.Stability.FieldIntegralReduction

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

instance conditionalGoeLaw_probability {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (r v : ℝ) (m z : ι → ℝ) : IsProbabilityMeasure (conditionalGoeLaw r v m z) := by
  unfold conditionalGoeLaw
  infer_instance

lemma conditionalFieldWeight_le_one {n : ℕ} [NeZero n] (j t σ : ℝ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (y : Fin n → ℝ) :
    conditionalFieldWeight j t σ E y ≤ 1 := prob_le_one

lemma conditionalFieldWeight_of_real_bound {n : ℕ} [NeZero n] {j t σ c : ℝ}
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (y : Fin n → ℝ)
    (hb : (conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (magnetization y) (empiricalObservation j t σ y)).real
      {W | (W,y)∈E} ≤ c) : conditionalFieldWeight j t σ E y ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_toReal (show conditionalFieldWeight j t σ E y ≠ ⊤ from measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hb

lemma measurable_scalarIntegrand {n : ℕ} [NeZero n] (j t σ : ℝ) :
    Measurable (scalarIntegrand (ι := Fin n) j t σ) := by
  unfold scalarIntegrand productNormal scalarEmpirical scalarPsi scalarA scalarD scalarS scalarM scalarQMoment
  simp only [integral_empiricalLaw]
  unfold gaussianPDFReal
  fun_prop

lemma scalar_density_prefactor_le_one {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (y : Fin n → ℝ) :
    sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y))) ≤ 1 := by
  have hq : 0 ≤ j*scalarQMoment (empiricalLaw y) := mul_nonneg hj (scalarQMoment_bounds _).1
  have hs : 0 < scalarS j (scalarEmpirical y t σ) := add_pos_of_pos_of_nonneg
    (add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)) hq
  exact sqrt_le_one.mpr ((div_le_one (add_pos_of_pos_of_nonneg hs hq)).mpr (le_add_of_nonneg_right hq))

lemma scalarIntegrand_nonneg {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    0 ≤ scalarIntegrand j t σ y := mul_nonneg (exp_pos _).le
      (Finset.prod_nonneg (fun i _=>gaussianPDFReal_nonneg _ _ (y i)))

lemma scalar_weighted_density_bound {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (y : Fin n → ℝ) {w b : ℝ≥0∞}
    (hw : w ≤ b) :
    ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*w ≤
    ENNReal.ofReal (scalarIntegrand j t σ y)*b := by
  apply mul_le_mul' _ hw
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_left (scalarIntegrand_nonneg j t σ y) (scalar_density_prefactor_le_one hj ht hσ y)

end SKGap
end
end

end OAI
