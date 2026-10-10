import OAI.Probability.FreeIsing.Gaussian.BinaryFusionJointLaw
import OAI.Probability.FreeIsing.Gaussian.LinearSignalTilt

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem binaryFusion_density_eq_mixture {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    (1 / 2 : ENNReal) * (ENNReal.ofReal (1 + u) * ENNReal.ofReal (1 + v)) +
      (1 / 2 : ENNReal) * (ENNReal.ofReal (1 - u) * ENNReal.ofReal (1 - v)) =
        ENNReal.ofReal (1 + u * v) := by
  have hpu : 0 ≤ 1 + u := by have := (abs_lt.mp hu).1; linarith
  have hpv : 0 ≤ 1 + v := by have := (abs_lt.mp hv).1; linarith
  have hmu : 0 ≤ 1 - u := by have := (abs_lt.mp hu).2; linarith
  have hmv : 0 ≤ 1 - v := by have := (abs_lt.mp hv).2; linarith
  have hh : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hh, ← ENNReal.ofReal_mul hpu, ← ENNReal.ofReal_mul hmu,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ (1 / 2 : ℝ) * ((1 + u) * (1 + v)))
      (by positivity : 0 ≤ (1 / 2 : ℝ) * ((1 - u) * (1 - v)))]
  congr 1
  ring

theorem linearSignalTilt_id_probability {mu : Measure ℝ}
    [IsProbabilityMeasure mu] {a : ℝ} (ha : |a| ≤ 1)
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hsym : Measure.map (fun u : ℝ => -u) mu = mu) :
    IsProbabilityMeasure (linearSignalTilt mu id a) := by
  apply linearSignalTilt_probability measurable_id (hu.mono (fun _ h => h.le)) ha
  exact integral_eq_zero_of_sign_reversal (MeasurableEquiv.neg ℝ)
    ⟨measurable_neg, hsym⟩ (fun _ => rfl)

theorem binaryFusionJointLaw_eq_conditional_mixture {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    (1 / 2 : ENNReal) •
        ((linearSignalTilt mu id 1).prod (linearSignalTilt nu id 1)) +
      (1 / 2 : ENNReal) •
        ((linearSignalTilt mu id (-1)).prod (linearSignalTilt nu id (-1))) =
      binaryFusionJointLaw mu nu := by
  unfold linearSignalTilt binaryFusionJointLaw
  simp only [id_eq, one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [prod_withDensity (by fun_prop) (by fun_prop),
    prod_withDensity (by fun_prop) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_add_left (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  exact binaryFusion_density_eq_mixture hp.1 hp.2

theorem binaryFusion_conditional_product_eq_tilt {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {a : ℝ}
    (ha : a = 1 ∨ a = -1)
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    (linearSignalTilt mu id a).prod (linearSignalTilt nu id a) =
      linearSignalTilt (binaryFusionJointLaw mu nu)
        (fun p => binaryFusion p.1 p.2) a := by
  have hab : |a| ≤ 1 := by rcases ha with rfl | rfl <;> norm_num
  unfold linearSignalTilt binaryFusionJointLaw
  rw [prod_withDensity (by fun_prop) (by fun_prop), ← withDensity_mul (mu.prod nu) (by fun_prop) (by unfold binaryFusion; fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  simp only [id_eq, Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (linearSignalTilt_density_nonneg hab hp.1.le),
    ← ENNReal.ofReal_mul (binaryFusion_denominator_pos hp.1 hp.2).le]
  congr 1
  have hd : 1 + p.1 * p.2 ≠ 0 := (binaryFusion_denominator_pos hp.1 hp.2).ne'
  unfold binaryFusion
  rcases ha with rfl | rfl <;> field_simp <;> ring

end Problem367

end

end OAI
