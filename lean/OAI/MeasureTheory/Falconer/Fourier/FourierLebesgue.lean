import OAI.MeasureTheory.Falconer.Fourier.FourierPairing
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate
open scoped ENNReal NNReal RealInnerProductSpace FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def sourceFourier (μ : Measure V) (ξ : V) : ℂ :=
  charFun μ ((-(2 * Real.pi)) • ξ)

theorem sourceFourier_integral_swap (μ : Measure V) [IsFiniteMeasure μ]
    (f : V → ℂ) (hf : Integrable f) :
    (∫ ξ, f ξ * sourceFourier μ ξ) = ∫ x, 𝓕 f x ∂μ := by
  have hi : Integrable (fun z : V × V =>
      f z.1 * Complex.exp (⟪z.2, (-(2*Real.pi)) • z.1⟫ * Complex.I))
      (volume.prod μ) := by
    apply (hf.norm.comp_fst μ).mono
    · exact hf.aestronglyMeasurable.comp_fst.mul (by fun_prop)
    · filter_upwards with z
      simp [Complex.norm_exp]
  simp only [sourceFourier, charFun_apply, ← integral_const_mul]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with x
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [inner_smul_right, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_ofNat, smul_eq_mul, real_inner_comm x ξ]
  ring_nf

theorem sourceFourier_difference (μ : Measure V) [IsFiniteMeasure μ] (ξ : V) :
    sourceFourier (μ ∗ μ.map (fun x => -x)) ξ = (‖sourceFourier μ ξ‖^2 : ℂ) := by
  have hr := charFun_map_smul (μ := μ) (-1 : ℝ) ((-(2*Real.pi)) • ξ)
  simp only [neg_one_smul, charFun_neg] at hr
  rw [sourceFourier, charFun_conv, hr, Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq _

theorem gaussian_lebesgue_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b * ‖ξ‖^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) hb 0 (0 : V)
  simpa [Complex.norm_exp, ← Complex.ofReal_pow] using h.norm

theorem source_gaussian_fourier {b : ℝ} (hb : 0 < b) (x : V) :
    𝓕 (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) x =
      ((Real.pi / b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2 / b) * ‖x‖^2) : ℝ) := by
  have he : (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) =
      (fun ξ : V => Complex.exp (-(b : ℂ) * ‖ξ‖^2)) := by
    funext ξ
    push_cast
    rfl
  rw [he, fourier_gaussian_innerProductSpace (b := (b : ℂ)) hb,
    Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1
  congr 1
  ring

theorem gaussian_lebesgue_square (μ : Measure V) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    (∫ ξ : V, Real.exp (-b * ‖ξ‖^2) * ‖sourceFourier μ ξ‖^2) =
      (Real.pi/b)^(Module.finrank ℝ V / 2 : ℝ) *
        ∫ x, ∫ y, Real.exp (-(Real.pi^2/b) * ‖x-y‖^2) ∂μ ∂μ := by
  let ρ := μ ∗ μ.map (fun x => -x)
  have hf : Integrable (fun ξ : V => (Real.exp (-b * ‖ξ‖^2) : ℂ)) :=
    (gaussian_lebesgue_integrable (V := V) hb).ofReal
  have h := sourceFourier_integral_swap ρ _ hf
  simp only [ρ, sourceFourier_difference, source_gaussian_fourier hb] at h
  have hconv : (∫ z : V, Real.exp (-(Real.pi^2/b) * ‖z‖^2) ∂ρ) =
      ∫ x, ∫ y, Real.exp (-(Real.pi^2/b) * ‖x-y‖^2) ∂μ ∂μ := by
    rw [show ρ = μ ∗ μ.map (fun x => -x) from rfl, integral_conv]
    · apply integral_congr_ae
      filter_upwards with x
      rw [integral_map (by fun_prop) (by fun_prop)]
      simp only [sub_eq_add_neg]
    · apply (integrable_const (1 : ℝ)).mono (by fun_prop)
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (sq_nonneg _) hb.le)) (sq_nonneg _)
  have hc : (∫ ξ : V, (Real.exp (-b * ‖ξ‖^2) * ‖sourceFourier μ ξ‖^2 : ℝ)) =
      ∫ x, (Real.pi/b)^(Module.finrank ℝ V / 2 : ℝ) *
        Real.exp (-(Real.pi^2/b) * ‖x‖^2) ∂ρ := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul, integral_complex_ofReal] using h
  rw [hc, integral_const_mul, hconv]

theorem source_scaled_gaussian_identity (μ : Measure V) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 < a) :
    (∫ x, ∫ y, Real.exp (-(Real.pi*a*‖x-y‖^2)) ∂μ ∂μ) =
      a^(-(Module.finrank ℝ V : ℝ)/2) *
        ∫ ξ : V, Real.exp (-Real.pi*‖ξ‖^2/a) * ‖sourceFourier μ ξ‖^2 := by
  have h := gaussian_lebesgue_square μ (div_pos Real.pi_pos ha)
  have h₁ : Real.pi / (Real.pi/a) = a := by field_simp
  have h₂ : Real.pi^2 / (Real.pi/a) = Real.pi*a := by field_simp
  rw [h₁,h₂] at h
  have he : (fun ξ : V => Real.exp (-(Real.pi/a)*‖ξ‖^2)*‖sourceFourier μ ξ‖^2) =
      (fun ξ : V => Real.exp (-Real.pi*‖ξ‖^2/a)*‖sourceFourier μ ξ‖^2) := by
    funext ξ
    congr 2
    ring
  rw [he] at h
  rw [h, neg_div, Real.rpow_neg ha.le, ← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos ha _).ne', one_mul]
  simp only [neg_mul, mul_assoc]

theorem gaussian_sourceFourier_integrable (μ : Measure V) [IsFiniteMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : V => Real.exp (-b*‖ξ‖^2)*‖sourceFourier μ ξ‖^2) := by
  apply ((gaussian_lebesgue_integrable (V := V) hb).mul_const ((μ.real univ)^2)).mono
  · unfold sourceFourier
    fun_prop
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

theorem source_scaled_gaussian_lintegral (μ : Measure V) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ z : V × V, ENNReal.ofReal (Real.exp (-(Real.pi*a*‖z.1-z.2‖^2))) ∂μ.prod μ) =
      ENNReal.ofReal (a^(-(Module.finrank ℝ V : ℝ)/2)) *
        ∫⁻ ξ : V, ENNReal.ofReal (Real.exp (-Real.pi*‖ξ‖^2/a)) *
          ENNReal.ofReal (‖sourceFourier μ ξ‖^2) := by
  have hi : Integrable (fun z : V × V => Real.exp (-(Real.pi*a*‖z.1-z.2‖^2)))
      (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono (by fun_prop)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hf : Integrable (fun ξ : V => Real.exp (-Real.pi*‖ξ‖^2/a)*‖sourceFourier μ ξ‖^2) := by
    convert gaussian_sourceFourier_integrable μ (div_pos Real.pi_pos ha) using 1
    funext ξ
    congr 2
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with z; positivity),
    integral_prod _ hi, source_scaled_gaussian_identity μ ha,
    ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hf (by filter_upwards with ξ; positivity)]
  congr 1
  apply lintegral_congr
  intro ξ
  exact ENNReal.ofReal_mul (Real.exp_pos _).le

end PlanarFalconer

end OAI
