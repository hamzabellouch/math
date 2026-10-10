import OAI.Probability.FreeIsing.Brownian.DriftMoments
import OAI.Probability.FreeIsing.Conditioning.InnovationConditionalMoments
import OAI.Probability.FreeIsing.Estimates.CharacteristicRecurrence
import OAI.Probability.FreeIsing.Martingales.GaussianCriterion

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem367.InnovationCharacteristic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integrable_increment_sq_of_bounded_drift
    {B W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hW : ∀ t, AEMeasurable (W t) P) {s t : ℝ≥0} (hst : s ≤ t)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ))) :
    Integrable (fun ω => (W t ω - W s ω) ^ 2) P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hK : 0 ≤ L * ((t : ℝ) - (s : ℝ)) := mul_nonneg hL (sub_nonneg.mpr hst)
  have h := integrable_abs_pow_of_bounded_perturbation 2 hK ((hW t).sub (hW s))
    (integrable_abs_pow_of_gaussianLaw (preBrownian_hasLaw_increment hB hst) 2) hbound
  simpa only [sq_abs, Pi.sub_apply] using h

theorem norm_integral_test_increment_sq_error_le
    {B W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hW : ∀ t, AEMeasurable (W t) P) {s t : ℝ≥0} (hst : s ≤ t)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hvariance : P[(fun ω => (B t ω - B s ω)^2) | m] =ᵐ[P]
      fun _ => (t : ℝ) - (s : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ)))
    {Z : Ω → ℂ} (hZ : StronglyMeasurable[m] Z)
    (hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    ‖∫ ω, Z ω * (((W t ω - W s ω : ℝ) : ℂ)^2 -
      (((t : ℝ) - (s : ℝ)) : ℂ)) ∂P‖ ≤
      2 * (L * ((t : ℝ) - (s : ℝ))) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        (L * ((t : ℝ) - (s : ℝ))) ^ 2 := by
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hD2 := integrable_increment_sq_of_bounded_drift hB hW hst hL hbound
  have hB2 : Integrable (fun ω => (B t ω - B s ω)^2) P := by
    simpa only [sq_abs] using
      integrable_abs_pow_of_gaussianLaw (preBrownian_hasLaw_increment hB hst) 2
  have htest := InnovationConditionalMoments.norm_integral_test_sub_const_le
    hm hD2 hB2 hvariance hZ (by norm_num : (0 : ℝ) ≤ 1) hZbound
  have hmoment := (preBrownian_bounded_drift_increment_moments hB hW hst hL hbound).2.1
  have heq : (fun ω => Z ω * (((W t ω - W s ω : ℝ) : ℂ)^2 -
      (((t : ℝ) - (s : ℝ)) : ℂ))) =
      (fun ω => ((W t ω - W s ω)^2 - ((t : ℝ) - (s : ℝ))) • Z ω) := by
    funext ω
    rw [Complex.real_smul]
    push_cast
    ring
  rw [heq]
  exact htest.trans (by simpa only [one_mul] using hmoment)

def driftMomentConstant (L : ℝ) : ℝ :=
  4 * standardGaussianThirdMoment + 4 * L ^ 3 + 2 * L + L ^ 2

theorem driftMomentConstant_nonneg {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ driftMomentConstant L := by
  have := standardGaussianThirdMoment_nonneg
  unfold driftMomentConstant
  positivity

theorem integral_increment_cube_le_common_constant
    {B W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hW : ∀ t, AEMeasurable (W t) P) {s t : ℝ≥0} (hst : s ≤ t)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ))) :
    (∫ ω, |W t ω - W s ω| ^ 3 ∂P) ≤ driftMomentConstant L *
      (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        ((t : ℝ) - (s : ℝ)) ^ 3) := by
  have hp := standardGaussianThirdMoment_nonneg
  have h1 : 4 * standardGaussianThirdMoment ≤ driftMomentConstant L := by
    unfold driftMomentConstant
    nlinarith [pow_nonneg hL 3, sq_nonneg L]
  have h2 : 4 * L ^ 3 ≤ driftMomentConstant L := by
    unfold driftMomentConstant
    nlinarith [pow_nonneg hL 3, sq_nonneg L]
  have htime : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr hst
  calc
    _ ≤ 4 * (standardGaussianThirdMoment * ((t : ℝ) - (s : ℝ)) *
        Real.sqrt ((t : ℝ) - (s : ℝ)) + (L * ((t : ℝ) - (s : ℝ))) ^ 3) :=
      (preBrownian_bounded_drift_increment_moments hB hW hst hL hbound).2.2.2
    _ = (4 * standardGaussianThirdMoment) *
        (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
        (4 * L ^ 3) * ((t : ℝ) - (s : ℝ)) ^ 3 := by ring
    _ ≤ driftMomentConstant L * (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
        driftMomentConstant L * ((t : ℝ) - (s : ℝ)) ^ 3 := by
      exact add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity))
        (mul_le_mul_of_nonneg_right h2 (by positivity))
    _ = _ := by ring

theorem norm_integral_test_increment_sq_error_le_common_constant
    {B W : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hW : ∀ t, AEMeasurable (W t) P) {s t : ℝ≥0} (hst : s ≤ t)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hvariance : P[(fun ω => (B t ω - B s ω)^2) | m] =ᵐ[P]
      fun _ => (t : ℝ) - (s : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ)))
    {Z : Ω → ℂ} (hZ : StronglyMeasurable[m] Z)
    (hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    ‖∫ ω, Z ω * (((W t ω - W s ω : ℝ) : ℂ)^2 -
      (((t : ℝ) - (s : ℝ)) : ℂ)) ∂P‖ ≤ driftMomentConstant L *
      (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        ((t : ℝ) - (s : ℝ)) ^ 2) := by
  let : MeasurableSpace Ω := mΩ
  have hp := standardGaussianThirdMoment_nonneg
  have h1 : 2 * L ≤ driftMomentConstant L := by unfold driftMomentConstant; nlinarith [pow_nonneg hL 3, sq_nonneg L]
  have h2 : L ^ 2 ≤ driftMomentConstant L := by unfold driftMomentConstant; nlinarith [pow_nonneg hL 3, sq_nonneg L]
  have htime : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr hst
  calc
    _ ≤ 2 * (L * ((t : ℝ) - (s : ℝ))) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        (L * ((t : ℝ) - (s : ℝ))) ^ 2 :=
      norm_integral_test_increment_sq_error_le hB hW hst hm hvariance hL hbound hZ hZbound
    _ = (2 * L) * (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
        L ^ 2 * ((t : ℝ) - (s : ℝ)) ^ 2 := by ring
    _ ≤ driftMomentConstant L * (((t : ℝ) - (s : ℝ)) * Real.sqrt ((t : ℝ) - (s : ℝ))) +
        driftMomentConstant L * ((t : ℝ) - (s : ℝ)) ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_right h1 (by positivity))
        (mul_le_mul_of_nonneg_right h2 (by positivity))
    _ = _ := by ring

theorem integral_characteristic_eq_gaussian_of_bounded_drift
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : Martingale W F P)
    (hvariance : ∀ a b : ℝ≥0, a ≤ b →
      P[(fun ω => (B b ω - B a ω)^2) | F a] =ᵐ[P]
        fun _ => (b : ℝ) - (a : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    (s T : ℝ≥0) (u : ℝ) (Z : Ω → ℂ)
    (hZ : StronglyMeasurable[F s] Z) (hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp ((-(u ^ 2 / 2) * (T : ℝ) : ℝ) : ℂ) * ∫ ω, Z ω ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hWm (t : ℝ≥0) : AEMeasurable (W t) P :=
    ((hW.stronglyMeasurable t).mono (F.le t)).measurable.aemeasurable
  apply integral_characteristic_eq_gaussian_of_martingale_moments P hW
    (driftMomentConstant_nonneg hL)
    (fun a b hab => integrable_increment_sq_of_bounded_drift hB hWm hab hL (hbound a b hab))
    (fun a b hab => (preBrownian_bounded_drift_increment_moments
      hB hWm hab hL (hbound a b hab)).2.2.1)
    (fun a b hab => integral_increment_cube_le_common_constant hB hWm hab hL (hbound a b hab))
    (fun a b hab Y hY hbY => by
      simpa only [Complex.ofReal_sub] using
        (norm_integral_test_increment_sq_error_le_common_constant
          hB hWm hab (F.le a) (hvariance a b hab) hL (hbound a b hab) hY hbY))
    s T u Z hZ hZbound

theorem integral_characteristic_eq_gaussian_of_independent_enlargement
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hmB : ∀ t, StronglyMeasurable (B t))
    (hW : Martingale W F P) {mSignal : MeasurableSpace Ω} (hSignal : mSignal ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap (fun ω t => B t ω) inferInstance) mSignal P)
    (hF : ∀ t, F t ≤ Filtration.natural B hmB t ⊔ mSignal)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    (s T : ℝ≥0) (u : ℝ) (Z : Ω → ℂ)
    (hZ : StronglyMeasurable[F s] Z) (hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1) :
    (∫ ω, Z ω * Complex.exp (((u * (W (s + T) ω - W s ω) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp ((-(u ^ 2 / 2) * (T : ℝ) : ℝ) : ℂ) * ∫ ω, Z ω ∂P := by
  let : MeasurableSpace Ω := mΩ
  exact integral_characteristic_eq_gaussian_of_bounded_drift hB hW
    (fun a b hab => InnovationConditionalMoments.preBrownian_increment_sq_condExp_enlarged
      hB hmB hSignal hind hab (hF a)) hL hbound s T u Z hZ hZbound

end Problem367.InnovationCharacteristic

end

end OAI
