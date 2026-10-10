import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import OAI.NumberTheory.Ostmann.QuadraticCenter.SignedQuadraticFrequency

namespace OAI

/-! # A positive band-limited Schwartz cutoff

A narrow real even smooth bump has a real Fourier transform bounded away from
zero on the unit interval. Squaring this transform gives the required cutoff;
its Fourier support is controlled by the convolution of the original bumps.
-/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexConjugate Convolution

private noncomputable def narrowBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 200, 1 / 100, by norm_num, by norm_num⟩

private noncomputable def narrowSchwartz : 𝓢(ℝ, ℂ) :=
  (narrowBump.hasCompactSupport.toSchwartzMap narrowBump.contDiff).postcompCLM Complex.ofRealCLM

private theorem narrowSchwartz_apply (x : ℝ) : narrowSchwartz x = (narrowBump x : ℂ) := rfl

private theorem narrowSchwartz_even (x : ℝ) : narrowSchwartz (-x) = narrowSchwartz x := by
  simp only [narrowSchwartz_apply, narrowBump.neg]

private theorem narrow_fourier_real (x : ℝ) :
    conj (𝓕 narrowSchwartz x) = 𝓕 narrowSchwartz x := by
  have hr := fourier_real_conj narrowSchwartz (by intro y; simp [narrowSchwartz_apply]) x
  change conj (𝓕 (narrowSchwartz : ℝ → ℂ) x) = 𝓕 (narrowSchwartz : ℝ → ℂ) x
  rw [← hr]
  have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
    (narrowSchwartz : ℝ → ℂ) x
  have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
    funext y
    exact narrowSchwartz_even y
  rw [hh] at he
  exact he.symm

private theorem narrow_fourier_lower (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y : ℝ, narrowBump y) / 2 ≤ (𝓕 narrowSchwartz x).re := by
  let phase : ℝ → ℂ := fun y => Complex.exp ((-2 * Real.pi * y * x : ℝ) * Complex.I)
  have hc : HasCompactSupport (fun y : ℝ => narrowSchwartz y) := by
    change HasCompactSupport (Complex.ofReal ∘ (narrowBump : ℝ → ℝ))
    exact narrowBump.hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 by simp)
  have hi : Integrable (fun y : ℝ => phase y * narrowSchwartz y) :=
    (by fun_prop : Continuous (fun y : ℝ => phase y * narrowSchwartz y)).integrable_of_hasCompactSupport hc.mul_left
  have hu : Integrable (narrowBump : ℝ → ℝ) :=
    narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport
  have hphase (y : ℝ) : (phase y * narrowSchwartz y).re =
      Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    simp only [phase, narrowSchwartz_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
  have hire := hi.re
  change Integrable (fun y => (phase y * narrowSchwartz y).re) at hire
  have hint : Integrable (fun y => Real.cos (-2 * Real.pi * y * x) * narrowBump y) := by
    simpa only [hphase] using hire
  have he : (𝓕 narrowSchwartz x).re = ∫ y : ℝ, Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    change (∫ y : ℝ, phase y * narrowSchwartz y).re = _
    have hh := integral_re hi
    change (∫ y : ℝ, (phase y * narrowSchwartz y).re) = (∫ y : ℝ, phase y * narrowSchwartz y).re at hh
    rw [← hh]
    simp only [hphase]
  rw [he, div_eq_mul_inv, ← integral_mul_const]
  apply integral_mono (hu.mul_const _) hint
  · intro y
    by_cases hy : narrowBump y = 0
    · simp [hy]
    have hylt : |y| < 1 / 100 := by
      have hm : y ∈ Function.support narrowBump := hy
      rw [narrowBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
      exact hm
    have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
    have hang : |(-2 * Real.pi * y * x)| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos Real.pi_pos]
      have hh := mul_le_mul (le_of_lt hylt) hxabs (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1 / 100)
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hcos : (1 / 2 : ℝ) ≤ Real.cos (-2 * Real.pi * y * x) := by
      have hs := (abs_le.mp hang)
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := -2 * Real.pi * y * x)]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right hcos (narrowBump.nonneg' y)

private theorem narrow_integral_pos : 0 < ∫ y : ℝ, narrowBump y := by
  apply integral_pos_of_integrable_nonneg_nonzero narrowBump.continuous
    (narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport)
    narrowBump.nonneg'
  have hh : narrowBump (0 : ℝ) = 1 := narrowBump.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]; exact narrowBump.rIn_pos.le)
  rw [hh]
  norm_num

private theorem schwartz_fourier_twice (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓕 (𝓕 f) x = f (-x) := by
  have hh := congrArg (fun g : 𝓢(ℝ, ℂ) => g (-x)) (show (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at hh
  exact hh

private theorem narrow_convolution_zero (x : ℝ) (hx : 1 ≤ |x|) :
    SchwartzMap.convolution (.mul ℂ ℂ) narrowSchwartz narrowSchwartz x = 0 := by
  rw [SchwartzMap.convolution_apply, convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : 1 / 100 ≤ |y|
  · have hz : narrowBump y = 0 := narrowBump.zero_of_le_dist (by simpa [Real.dist_eq, narrowBump] using hy)
    simp [narrowSchwartz_apply, hz]
  · have hxy : 1 / 100 ≤ |x - y| := by
      have hh := abs_add_le (x - y) y
      rw [sub_add_cancel] at hh
      linarith
    have hz : narrowBump (x - y) = 0 := narrowBump.zero_of_le_dist (by simpa [Real.dist_eq, narrowBump] using hxy)
    simp [narrowSchwartz_apply, hz]

/-- The cutoff needed by the original amplified moment argument exists. -/
theorem exists_positive_even_fourier_cutoff :
    ∃ (c : ℝ) (ψ : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, conj (ψ x) = ψ x) ∧ (∀ x, 0 ≤ (ψ x).re) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ x).re) ∧
      (∀ x : ℝ, (3 : ℝ) ^ 2 < |x| → 𝓕 ψ x = 0) ∧
      (∀ x : ℝ, 𝓕 ψ (-x) = 𝓕 ψ x) := by
  let f := 𝓕 narrowSchwartz
  let ψ := SchwartzMap.pairing (.mul ℂ ℂ) f f
  let c := ((∫ y : ℝ, narrowBump y) / 2) ^ 2
  have hfreal (x : ℝ) : (f x).im = 0 := by
    have hh := congrArg Complex.im (narrow_fourier_real x)
    simp only [Complex.conj_im] at hh
    change -(f x).im = (f x).im at hh
    linarith
  have hψ (x : ℝ) : ψ x = f x * f x := rfl
  have hcpos := narrow_integral_pos
  refine ⟨c, ψ, by dsimp [c]; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [hψ, map_mul] using congrArg (fun z : ℂ => z * z) (narrow_fourier_real x)
  · intro x
    rw [hψ, Complex.mul_re, hfreal]
    nlinarith
  · intro x hx
    rw [hψ, Complex.mul_re, hfreal]
    have hl := narrow_fourier_lower x hx
    change (∫ y : ℝ, narrowBump y) / 2 ≤ (f x).re at hl
    dsimp [c]
    nlinarith [narrow_integral_pos]
  · intro x hx
    have he : ψ = 𝓕 (SchwartzMap.convolution (.mul ℂ ℂ) narrowSchwartz narrowSchwartz) :=
      (SchwartzMap.fourier_convolution _ _ _).symm
    rw [he, schwartz_fourier_twice]
    exact narrow_convolution_zero (-x) (by rw [abs_neg]; linarith)

  · intro x
    have hfEven (y : ℝ) : f (-y) = f y := by
      have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (narrowSchwartz : ℝ → ℂ) y
      have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
        funext z
        exact narrowSchwartz_even z
      rw [hh] at he
      exact he.symm
    have hψEven : (ψ : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = ψ := by
      funext y
      change f (-y) * f (-y) = f y * f y
      rw [hfEven]
    have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
      (ψ : ℝ → ℂ) x
    rw [hψEven] at he
    exact he.symm

/-- A positive Fourier cutoff with bounded derivatives and compact Fourier support. -/
theorem exists_positive_fourier_cutoff :
    ∃ (c : ℝ) (ψ : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, conj (ψ x) = ψ x) ∧ (∀ x, 0 ≤ (ψ x).re) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ x).re) ∧
      (∀ x : ℝ, (3 : ℝ) ^ 2 < |x| → 𝓕 ψ x = 0) := by
  obtain ⟨c, ψ, hc, hr, hp, hl, hs, _⟩ := exists_positive_even_fourier_cutoff
  exact ⟨c, ψ, hc, hr, hp, hl, hs⟩

/-- The compact bump itself localizes a Dirichlet polynomial while its Fourier
transform is bounded below throughout the unit height window. -/
theorem exists_density_localizer :
    ∃ (c : ℝ) (W : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, 1 ≤ |x| → W x = 0) ∧ (∀ x, ‖W x‖ ≤ 1) ∧
      (∀ t, |t| ≤ 1 → c ≤ ‖𝓕 W t‖) := by
  refine ⟨(∫ y : ℝ, narrowBump y) / 2, narrowSchwartz,
    div_pos narrow_integral_pos (by norm_num), ?_, ?_, ?_⟩
  · intro x hx
    have hz : narrowBump x = 0 := narrowBump.zero_of_le_dist (by
      change 1 / 100 ≤ |x - 0|
      rw [sub_zero]
      linarith)
    simp only [narrowSchwartz_apply, hz, Complex.ofReal_zero]
  · intro x
    rw [narrowSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (narrowBump.nonneg' x)]
    exact narrowBump.le_one
  · intro t ht
    have heven (y : ℝ) : 𝓕 narrowSchwartz (-y) = 𝓕 narrowSchwartz y := by
      have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (narrowSchwartz : ℝ → ℂ) y
      have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
        funext z
        exact narrowSchwartz_even z
      rw [hh] at he
      exact he.symm
    have habs : ‖𝓕 narrowSchwartz |t|‖ = ‖𝓕 narrowSchwartz t‖ := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, heven]
    rw [← habs]
    exact (narrow_fourier_lower |t| ⟨abs_nonneg t, ht⟩).trans (Complex.re_le_norm _)

end Ostmann

end OAI
