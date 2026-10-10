import OAI.Probability.SpanningForest.CharacteristicRemainder
import OAI.Probability.SpanningForest.GaussianBoundedCorrection
import OAI.Probability.SpanningForest.GaussianMomentScaling

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.Innovation

theorem conditional_square_perturbation_le
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (hm : m ≤ mΩ) {Q R : Ω → ℝ} {a : ℝ}
    (hQ : Integrable Q P) (hQ2 : Integrable (fun ω => Q ω ^ 2) P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂P, |R ω| ≤ a) :
    ∀ᵐ ω ∂P,
      |P[fun ω => (Q ω + R ω) ^ 2 | m] ω - P[fun ω => Q ω ^ 2 | m] ω| ≤
      2 * a * P[fun ω => |Q ω| | m] ω + a ^ 2 := by
  have hD2 := GaussianBoundedCorrection.integrable_sq_add_of_bounded hQ.aestronglyMeasurable
    hQ2 hR ha hbound
  let Δ : Ω → ℝ := fun ω => (Q ω + R ω)^2 - Q ω^2
  have hΔ : Integrable Δ P := hD2.sub hQ2
  have hdom : Integrable (fun ω => 2 * a * |Q ω| + a^2) P :=
    (hQ.abs.const_mul (2 * a)).add (integrable_const _)
  have hmono := condExp_mono (m := m) hΔ.abs hdom (by
    filter_upwards [hbound] with ω hω
    exact GaussianBoundedCorrection.abs_sq_add_sub_sq_le (Q ω) (R ω) a ha hω)
  have hscale : P[fun ω => 2 * a * |Q ω| | m] =ᵐ[P]
      (fun ω => 2 * a * P[fun ω => |Q ω| | m] ω) := by
    have h := condExp_smul (μ := P) (2 * a) (fun ω => |Q ω|) m
    exact h
  filter_upwards [abs_condExp_ae_le_condExp_abs (m := m) Δ, hmono,
    condExp_sub hD2 hQ2 m, condExp_add (hQ.abs.const_mul (2*a)) (integrable_const (a^2)) m,
    hscale] with ω hn hmonoω hsub hadd hscaleω
  change |P[Δ | m] ω| ≤ P[fun ω => |Δ ω| | m] ω at hn
  change P[Δ | m] ω = P[fun ω => (Q ω + R ω)^2 | m] ω - P[fun ω => Q ω^2 | m] ω at hsub
  change P[fun ω => 2*a*|Q ω| + a^2 | m] ω =
    P[fun ω => 2*a*|Q ω| | m] ω + P[fun _ => a^2 | m] ω at hadd
  rw [hadd, hscaleω, condExp_const hm] at hmonoω
  rw [hsub] at hn
  exact hn.trans hmonoω

theorem conditional_cube_perturbation_le
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (hm : m ≤ mΩ) {Q R : Ω → ℝ} {a : ℝ}
    (hQ : AEStronglyMeasurable Q P) (hQ3 : Integrable (fun ω => |Q ω| ^ 3) P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂P, |R ω| ≤ a) :
    ∀ᵐ ω ∂P,
      P[fun ω => |Q ω + R ω| ^ 3 | m] ω ≤
      4 * (P[fun ω => |Q ω| ^ 3 | m] ω + a ^ 3) := by
  have hD3 := GaussianBoundedCorrection.integrable_abs_cube_add_of_bounded hQ hQ3 hR ha hbound
  have hdom : Integrable (fun ω => 4 * (|Q ω|^3 + a^3)) P :=
    (hQ3.add (integrable_const _)).const_mul _
  have hmono := condExp_mono (m := m) hD3 hdom (by
    filter_upwards [hbound] with ω hω
    exact GaussianBoundedCorrection.abs_add_cube_le (Q ω) (R ω) a ha hω)
  have hscale : P[fun ω => 4 * (|Q ω|^3 + a^3) | m] =ᵐ[P]
      (fun ω => 4 * P[fun ω => |Q ω|^3 + a^3 | m] ω) :=
    condExp_smul (μ := P) (4 : ℝ) (fun ω => |Q ω|^3 + a^3) m
  filter_upwards [hmono, hscale, condExp_add hQ3 (integrable_const (a^3)) m]
    with ω hmonoω hscaleω hadd
  change P[fun ω => |Q ω|^3 + a^3 | m] ω =
    P[fun ω => |Q ω|^3 | m] ω + P[fun _ => a^3 | m] ω at hadd
  rw [hscaleω, hadd, condExp_const hm] at hmonoω
  exact hmonoω

theorem conditional_noise_function_eq_integral
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    (hm : m ≤ mΩ) {Q : Ω → ℝ} (hQ : Measurable Q)
    (hindep : Indep (MeasurableSpace.comap Q (inferInstance : MeasurableSpace ℝ)) m P)
    {f : ℝ → ℝ} (hf : Measurable f) :
    P[fun ω => f (Q ω) | m] =ᵐ[P] fun _ => ∫ ω, f (Q ω) ∂P := by
  exact condExp_indep_eq hQ.comap_le hm
    (hf.comp (comap_measurable Q)).stronglyMeasurable hindep

theorem conditional_gaussian_bounded_correction_error
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hm : m ≤ mΩ) {Q R : Ω → ℝ} {v : ℝ≥0} {a : ℝ}
    (hQ : HasLaw Q (gaussianReal 0 v) P) (hQmeas : Measurable Q)
    (hindep : Indep (MeasurableSpace.comap Q (inferInstance : MeasurableSpace ℝ)) m P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂P, |R ω| ≤ a)
    (hcenter : P[fun ω => Q ω + R ω | m] =ᵐ[P] 0)
    (hv : (v : ℝ) ≤ 2) :
    ∀ᵐ ω ∂P,
      ‖P[fun ω => Complex.exp (((Q ω + R ω : ℝ) : ℂ) * Complex.I) | m] ω -
        Complex.exp (-(v : ℂ) / 2)‖ ≤
      16 * (Real.sqrt v ^ 3 * GaussianBoundedCorrection.standardGaussianAbsMoment 3 + a ^ 3) +
        (2 * a * Real.sqrt v + a ^ 2) / 2 + (v : ℝ) ^ 2 / 4 := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  have hQi := hQ.hasGaussianLaw.integrable
  have hQ2 : Integrable (fun ω => Q ω^2) P := by
    simpa only [sq_abs] using gaussian_hasLaw_integrable_abs_pow hQ 2
  have hQ3 := gaussian_hasLaw_integrable_abs_pow hQ 3
  have hRi : Integrable R P := Integrable.of_bound hR a (by
    simpa only [Real.norm_eq_abs] using hbound)
  have hD2 := GaussianBoundedCorrection.integrable_sq_add_of_bounded hQi.aestronglyMeasurable
    hQ2 hR ha hbound
  have hD3 := GaussianBoundedCorrection.integrable_abs_cube_add_of_bounded
    hQi.aestronglyMeasurable hQ3 hR ha hbound
  have hqcond₂ := conditional_noise_function_eq_integral hm hQmeas hindep
    (show Measurable (fun x : ℝ => x^2) by fun_prop)
  have hqcond₁ := conditional_noise_function_eq_integral hm hQmeas hindep
    (show Measurable (fun x : ℝ => |x|) by fun_prop)
  have hqcond₃ := conditional_noise_function_eq_integral hm hQmeas hindep
    (show Measurable (fun x : ℝ => |x|^3) by fun_prop)
  have hsecond : ∀ᵐ ω ∂P,
      |P[fun ω => (Q ω + R ω)^2 | m] ω - (v : ℝ)| ≤ 2*a*Real.sqrt v + a^2 := by
    filter_upwards [conditional_square_perturbation_le hm hQi hQ2 hR ha hbound,
      hqcond₂, hqcond₁] with ω hb h₂ h₁
    rw [h₂, h₁, gaussian_hasLaw_second_moment hQ] at hb
    have hc : 0 ≤ 2 * a := mul_nonneg (by norm_num) ha
    exact hb.trans (add_le_add
      (mul_le_mul_of_nonneg_left (gaussian_hasLaw_absolute_first_moment_le hQ) hc) le_rfl)
  have hthird : ∀ᵐ ω ∂P, P[fun ω => |Q ω + R ω|^3 | m] ω ≤
      4 * (Real.sqrt v^3 * GaussianBoundedCorrection.standardGaussianAbsMoment 3 + a^3) := by
    filter_upwards [conditional_cube_perturbation_le hm hQi.aestronglyMeasurable hQ3 hR ha hbound,
      hqcond₃] with ω hb h₃
    rw [h₃, GaussianBoundedCorrection.hasLaw_gaussian_abs_moment hQ 3] at hb
    exact hb
  have h := conditional_characteristic_error hm (hQi.add hRi) hD2 hD3
    v.coe_nonneg hv hcenter hsecond hthird
  simpa only [Pi.add_apply, ← mul_assoc, show (4 : ℝ) * 4 = 16 by norm_num] using h

theorem gaussian_correction_error_rate
    {h L σ c : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) :
    16 * (Real.sqrt (h * σ^2)^3 * c + (h*L)^3) +
        (2*(h*L)*Real.sqrt (h*σ^2) + (h*L)^2)/2 + (h*σ^2)^2/4 ≤
      (16*(σ^3*c + L^3) + L*σ + L^2/2 + σ^4/4) * (h*Real.sqrt h) := by
  have hr₀ : 0 ≤ Real.sqrt h := Real.sqrt_nonneg h
  have hr₁ : Real.sqrt h ≤ 1 := Real.sqrt_le_one.mpr hh₁
  have hr₂ : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh
  have hhroot : h ≤ Real.sqrt h := by nlinarith
  have hh₂ : h^2 ≤ h*Real.sqrt h := by nlinarith
  have hh₃ : h^3 ≤ h*Real.sqrt h := by
    have h32 : h^3 ≤ h^2 := by nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh₁)]
    exact h32.trans hh₂
  have hroot₃ : Real.sqrt h ^ 3 = h * Real.sqrt h := by
    calc
      _ = Real.sqrt h ^ 2 * Real.sqrt h := by ring
      _ = _ := by rw [hr₂]
  calc
    _ = 16*σ^3*c*(h*Real.sqrt h) + 16*L^3*h^3 +
        L*σ*(h*Real.sqrt h) + (L^2/2)*h^2 + (σ^4/4)*h^2 := by
      rw [Real.sqrt_mul hh, Real.sqrt_sq hσ]
      simp only [mul_pow, hroot₃]
      ring
    _ ≤ 16*σ^3*c*(h*Real.sqrt h) + 16*L^3*(h*Real.sqrt h) +
        L*σ*(h*Real.sqrt h) + (L^2/2)*(h*Real.sqrt h) +
        (σ^4/4)*(h*Real.sqrt h) := by
      gcongr
    _ = _ := by ring

theorem conditional_gaussian_increment_error
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hm : m ≤ mΩ) {Q R : Ω → ℝ} {v : ℝ≥0} {h L σ : ℝ}
    (hQ : HasLaw Q (gaussianReal 0 v) P) (hQmeas : Measurable Q)
    (hindep : Indep (MeasurableSpace.comap Q (inferInstance : MeasurableSpace ℝ)) m P)
    (hR : AEStronglyMeasurable R P) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hvariance : (v : ℝ) = h*σ^2)
    (hbound : ∀ᵐ ω ∂P, |R ω| ≤ h*L)
    (hcenter : P[fun ω => Q ω + R ω | m] =ᵐ[P] 0)
    (hv : (v : ℝ) ≤ 2) :
    ∀ᵐ ω ∂P,
      ‖P[fun ω => Complex.exp (((Q ω + R ω : ℝ) : ℂ) * Complex.I) | m] ω -
        Complex.exp (-(v : ℂ) / 2)‖ ≤
      (16*(σ^3*GaussianBoundedCorrection.standardGaussianAbsMoment 3 + L^3) +
        L*σ + L^2/2 + σ^4/4) * (h*Real.sqrt h) := by
  have hlocal := conditional_gaussian_bounded_correction_error hm hQ hQmeas hindep hR
    (mul_nonneg hh hL) hbound hcenter hv
  filter_upwards [hlocal] with ω hω
  apply hω.trans
  rw [hvariance]
  exact gaussian_correction_error_rate hh hh₁ hL hσ

end Problem336.Innovation

end

end OAI
