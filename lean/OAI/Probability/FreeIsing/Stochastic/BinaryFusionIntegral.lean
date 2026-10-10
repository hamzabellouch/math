import OAI.Probability.FreeIsing.Gaussian.BinaryFusion

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem ae_binaryFusion_bounds {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    ∀ᵐ p ∂mu.prod nu, |p.1| < 1 ∧ |p.2| < 1 := by
  have hu' : ∀ᵐ p ∂mu.prod nu, |p.1| < 1 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hu
  have hv' : ∀ᵐ p ∂mu.prod nu, |p.2| < 1 :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae hv
  exact hu'.and hv'

theorem integrable_binaryFusion_integrand {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    Integrable (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 / (1 + p.1 * p.2))
      (mu.prod nu) := by
  refine (integrable_const (2 : ℝ)).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (sq_nonneg _) (binaryFusion_denominator_pos hp.1 hp.2).le)]
  exact binaryFusion_integrand_le_two hp.1 hp.2

theorem integrable_binaryFusionLoss {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    Integrable (fun p : ℝ × ℝ => binaryFusionLoss p.1 p.2) (mu.prod nu) := by
  refine (integrable_const (2 : ℝ)).mono' ?_ ?_
  · unfold binaryFusionLoss
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (binaryFusionLoss_nonneg hp.1 hp.2)]
    have h := binaryFusionLoss_le_sum_sq hp.1 hp.2
    have hu' := (sq_lt_one_iff_abs_lt_one p.1).mpr hp.1
    have hv' := (sq_lt_one_iff_abs_lt_one p.2).mpr hp.2
    linarith

theorem integral_binaryFusion_symmetric_square {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu) =
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  let R : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
  have hR : MeasurePreserving R (mu.prod nu) (mu.prod nu) :=
    (MeasurePreserving.id mu).prod ⟨measurable_neg, hsym⟩
  have hi := integrable_binaryFusion_integrand hu hv
  have hin : Integrable (fun p : ℝ × ℝ =>
      (p.1 - p.2) ^ 2 / (1 - p.1 * p.2)) (mu.prod nu) := by
    have h := (hR.integrable_comp hi.aestronglyMeasurable).mpr hi
    change Integrable (fun p : ℝ × ℝ =>
      (p.1 + -p.2) ^ 2 / (1 + p.1 * -p.2)) (mu.prod nu) at h
    simpa [sub_eq_add_neg] using h
  have heq : (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 / (1 - p.1 * p.2) ∂mu.prod nu) =
      ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu := by
    have h := hR.integral_comp'
      (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 / (1 + p.1 * p.2))
    change (∫ p : ℝ × ℝ, (p.1 + -p.2) ^ 2 / (1 + p.1 * -p.2) ∂mu.prod nu) = _ at h
    simpa [sub_eq_add_neg] using h
  have hiu : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (mu.prod nu) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p.1)] using
      ((sq_lt_one_iff_abs_lt_one p.1).mpr hp.1).le
  have hiv : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (mu.prod nu) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p.2)] using
      ((sq_lt_one_iff_abs_lt_one p.2).mpr hp.2).le
  have hl := integrable_binaryFusionLoss hu hv
  have hiuv : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (mu.prod nu) := hiu.add hiv
  have hsum : (∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 ∂mu.prod nu) =
      (∫ p : ℝ × ℝ, p.1 ^ 2 ∂mu.prod nu) +
        ∫ p : ℝ × ℝ, p.2 ^ 2 ∂mu.prod nu := integral_add hiu hiv
  have hscalar :
      (∫ p : ℝ × ℝ,
        ((p.1 + p.2) ^ 2 / (1 + p.1 * p.2) +
          (p.1 - p.2) ^ 2 / (1 - p.1 * p.2)) / 2 ∂mu.prod nu) =
      ∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 - binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
    apply integral_congr_ae
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    exact binaryFusion_symmetric_square hp.1 hp.2
  rw [integral_div, integral_add hi hin, heq,
    integral_sub hiuv hl, hsum,
    integral_fun_fst (μ := mu) (ν := nu) (fun u : ℝ => u ^ 2),
    integral_fun_snd (μ := mu) (ν := nu) (fun v : ℝ => v ^ 2)] at hscalar
  simp only [probReal_univ, one_smul] at hscalar
  linarith

theorem integral_binaryFusionLoss_nonneg {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    0 ≤ ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  exact binaryFusionLoss_nonneg hp.1 hp.2

theorem integral_binaryFusion_le_sum_sq {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu) ≤
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) := by
  rw [integral_binaryFusion_symmetric_square hu hv hsym]
  exact sub_le_self _ (integral_binaryFusionLoss_nonneg hu hv)

private theorem integrable_sq_of_ae_abs_lt_one {mu : Measure ℝ}
    [IsProbabilityMeasure mu] (hu : ∀ᵐ u ∂mu, |u| < 1) :
    Integrable (fun u : ℝ => u ^ 2) mu := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [hu] with u hu
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)] using
    ((sq_lt_one_iff_abs_lt_one u).mpr hu).le

theorem integral_binaryFusionLoss_lower_bound {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {theta : ℝ}
    (hu : ∀ᵐ u ∂mu, |u| ≤ theta) (hv : ∀ᵐ v ∂nu, |v| ≤ theta)
    (htheta : theta < 1) :
    2 * (1 - theta ^ 2) * (∫ u : ℝ, u ^ 2 ∂mu) * (∫ v : ℝ, v ^ 2 ∂nu) ≤
      ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  have hu1 : ∀ᵐ u ∂mu, |u| < 1 := hu.mono (fun _ h => lt_of_le_of_lt h htheta)
  have hv1 : ∀ᵐ v ∂nu, |v| < 1 := hv.mono (fun _ h => lt_of_le_of_lt h htheta)
  have hiu := integrable_sq_of_ae_abs_lt_one hu1
  have hiv := integrable_sq_of_ae_abs_lt_one hv1
  have hip := hiu.mul_prod hiv
  have hl := integrable_binaryFusionLoss hu1 hv1
  have hu' : ∀ᵐ p ∂mu.prod nu, |p.1| ≤ theta :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hu
  have hv' : ∀ᵐ p ∂mu.prod nu, |p.2| ≤ theta :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae hv
  have hb : (∫ p : ℝ × ℝ, (2 * (1 - theta ^ 2)) * (p.1 ^ 2 * p.2 ^ 2) ∂mu.prod nu) ≤
      ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
    apply integral_mono_ae (hip.const_mul _) hl
    filter_upwards [hu', hv'] with p hpu hpv
    simpa only [mul_assoc] using binaryFusionLoss_lower_bound hpu hpv htheta
  rw [integral_const_mul,
    integral_prod_mul (μ := mu) (ν := nu) (fun u : ℝ => u ^ 2) (fun v : ℝ => v ^ 2)] at hb
  simpa only [mul_assoc] using hb

theorem integral_binaryFusion_le_sum_sq_sub_loss {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {theta : ℝ}
    (hu : ∀ᵐ u ∂mu, |u| ≤ theta) (hv : ∀ᵐ v ∂nu, |v| ≤ theta)
    (htheta : theta < 1) (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu) ≤
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) -
        2 * (1 - theta ^ 2) * (∫ u : ℝ, u ^ 2 ∂mu) * (∫ v : ℝ, v ^ 2 ∂nu) := by
  have hu1 : ∀ᵐ u ∂mu, |u| < 1 := hu.mono (fun _ h => lt_of_le_of_lt h htheta)
  have hv1 : ∀ᵐ v ∂nu, |v| < 1 := hv.mono (fun _ h => lt_of_le_of_lt h htheta)
  rw [integral_binaryFusion_symmetric_square hu1 hv1 hsym]
  exact sub_le_sub_left (integral_binaryFusionLoss_lower_bound hu hv htheta) _

end Problem367

end

end OAI
