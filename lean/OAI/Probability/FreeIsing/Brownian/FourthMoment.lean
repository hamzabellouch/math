import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367

def standardGaussianFourthMoment : ℝ :=
  ∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 1

theorem standardGaussianFourthMoment_nonneg : 0 ≤ standardGaussianFourthMoment := by
  exact integral_nonneg fun x => pow_nonneg (norm_nonneg x) 4

theorem integrable_gaussian_norm_fourth (v : ℝ≥0) :
    Integrable (fun x : ℝ => ‖x‖ ^ 4) (gaussianReal 0 v) := by
  exact (memLp_id_gaussianReal' (μ := 0) (v := v) 4 (by norm_num)).integrable_norm_pow
    (by norm_num)

theorem gaussian_norm_fourth_eq (v : ℝ≥0) :
    (∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 v) =
      standardGaussianFourthMoment * (v : ℝ) ^ 2 := by
  have hm : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v : ℝ) * x) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    apply Subtype.ext
    exact Real.sq_sqrt v.property
  rw [← hm, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [norm_mul, mul_pow]
  rw [integral_const_mul]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpow : Real.sqrt (v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    calc
      Real.sqrt (v : ℝ) ^ 4 = (Real.sqrt (v : ℝ) ^ 2) ^ 2 := by ring
      _ = (v : ℝ) ^ 2 := congrArg (fun r : ℝ => r ^ 2) (Real.sq_sqrt v.property)
  rw [hpow]
  exact mul_comm _ _

theorem preBrownian_increment_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, ‖B t ω - B s ω‖ ^ 4 ∂P) =
      standardGaussianFourthMoment * |(t : ℝ) - (s : ℝ)| ^ 2 := by
  have hL := hB.hasLaw_sub t s
  have hi := hL.integral_comp (f := fun x : ℝ => ‖x‖ ^ 4) (by fun_prop)
  simpa only [Function.comp_def, Pi.sub_apply, coe_nndist, Real.dist_eq] using
    hi.trans (gaussian_norm_fourth_eq (nndist (t : ℝ) (s : ℝ)))

theorem integrable_preBrownian_increment_fourth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    Integrable (fun ω => ‖B t ω - B s ω‖ ^ 4) P := by
  exact ((hB.hasLaw_sub t s).hasGaussianLaw.memLp (p := 4)
    (by norm_num)).integrable_norm_pow (by norm_num)

theorem preBrownian_isKolmogorovProcess
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) :
    IsKolmogorovProcess B P 4 2
      (NNReal.mk standardGaussianFourthMoment standardGaussianFourthMoment_nonneg) := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology hm _ (by norm_num) (by norm_num)
  intro s t
  have hi := ofReal_integral_eq_lintegral_ofReal
    (integrable_preBrownian_increment_fourth hB t s)
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (norm_nonneg (B s ω - B t ω)) 4))
  rw [preBrownian_increment_fourth_moment hB t s] at hi
  have he : (∫⁻ ω, edist (B s ω) (B t ω) ^ (4 : ℝ) ∂P) =
      ENNReal.ofReal standardGaussianFourthMoment *
        edist s t ^ (2 : ℝ) := by
    simpa only [edist_dist, dist_eq_norm, NNReal.dist_eq, ENNReal.rpow_ofNat,
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (abs_nonneg _),
      ← ENNReal.ofReal_mul standardGaussianFourthMoment_nonneg,
      ENNReal.ofReal_coe_nnreal] using hi.symm
  simpa only [ENNReal.coe_nnreal_eq, NNReal.coe_mk] using he.le

end Problem367

end

end OAI
