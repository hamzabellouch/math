import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.SchwartzCutoff
open scoped FourierTransform SchwartzMap Convolution ComplexConjugate
open MeasureTheory Complex Set Metric

def bump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 16, 1 / 8, by norm_num, by norm_num⟩

lemma bump_zero : bump 0 = 1 :=
  bump.one_of_mem_closedBall (by simp [bump])

lemma bump_complex_compact : HasCompactSupport (fun x : ℝ => (bump x : ℂ)) :=
  bump.hasCompactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) rfl

def bumpSchwartz : SchwartzMap ℝ ℂ :=
  bump_complex_compact.toSchwartzMap (Complex.ofRealCLM.contDiff.comp bump.contDiff)

@[simp] lemma bumpSchwartz_apply (x : ℝ) : bumpSchwartz x = (bump x : ℂ) := rfl

lemma fourier_real_conj (g : ℝ → ℝ) (x : ℝ) :
    conj (𝓕 (fun t => (g t : ℂ)) x) = 𝓕 (fun t => (g t : ℂ)) (-x) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_mul, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I]
  congr 2
  push_cast
  ring

lemma bump_fourier_even (x : ℝ) : 𝓕 bumpSchwartz (-x) = 𝓕 bumpSchwartz x := by
  change 𝓕 (fun t => (bump t : ℂ)) (-x) = 𝓕 (fun t => (bump t : ℂ)) x
  have h := Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) (fun t => (bump t : ℂ)) x
  change 𝓕 (fun t : ℝ => (bump (-t) : ℂ)) x = 𝓕 (fun t => (bump t : ℂ)) (-x) at h
  simpa only [bump.neg] using h.symm

lemma bump_fourier_im (x : ℝ) : (𝓕 bumpSchwartz x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  exact (fourier_real_conj bump x).trans (bump_fourier_even x)

lemma bump_fourier_re (x : ℝ) :
    (𝓕 bumpSchwartz x).re = ∫ t : ℝ, Real.cos (-2 * Real.pi * t * x) * bump t := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp only [bumpSchwartz_apply, smul_eq_mul]
  have hc : HasCompactSupport
      (fun t : ℝ => Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) * (bump t : ℂ)) :=
    bump_complex_compact.mul_left
  have hb : Continuous (fun t : ℝ => bump t) := bump.continuous
  have hi : Integrable
      (fun t : ℝ => Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) * (bump t : ℂ)) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport hc
  have hre := integral_re hi
  change (∫ t : ℝ, (Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) * (bump t : ℂ)).re) =
    (∫ t : ℝ, Complex.exp ((-2 * Real.pi * t * x : ℝ) * Complex.I) * (bump t : ℂ)).re at hre
  rw [← hre]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]

lemma bump_fourier_re_pos {x : ℝ} (hx : |x| ≤ 1) : 0 < (𝓕 bumpSchwartz x).re := by
  rw [bump_fourier_re]
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f := fun t : ℝ => Real.cos (-2 * Real.pi * t * x) * bump t) (x := 0)
  · exact (by fun_prop : Continuous (fun t : ℝ => Real.cos (-2 * Real.pi * t * x))).mul bump.continuous
  · exact bump.hasCompactSupport.mul_left
  · intro t
    by_cases ht : bump t = 0
    · simp [ht]
    · have htr : |t| < 1 / 8 := by
        have hm : t ∈ Function.support bump := ht
        rw [bump.support_eq] at hm
        simpa [bump, Real.dist_eq] using hm
      have habs : |-2 * Real.pi * t * x| < Real.pi / 2 := by
        have hprod : |t| * |x| ≤ |t| := by
          simpa using mul_le_mul_of_nonneg_left hx (abs_nonneg t)
        calc
          |-2 * Real.pi * t * x| = 2 * Real.pi * (|t| * |x|) := by
            simp only [abs_mul, abs_of_nonneg Real.pi_pos.le]
            norm_num
            ring
          _ ≤ 2 * Real.pi * |t| := mul_le_mul_of_nonneg_left hprod (by positivity)
          _ < Real.pi / 2 := by nlinarith [Real.pi_pos]
      have hc := Real.cos_pos_of_mem_Ioo (abs_lt.mp habs)
      exact mul_nonneg hc.le bump.nonneg
  · simp [bump_zero]

theorem bump_fourier_uniform_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, |x| ≤ 1 → c ≤ ‖𝓕 bumpSchwartz x‖ := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    ((Complex.continuous_re.comp (𝓕 bumpSchwartz).continuous).continuousOn)
  refine ⟨(𝓕 bumpSchwartz x₀).re, bump_fourier_re_pos (abs_le.mpr hx₀), ?_⟩
  intro x hx
  exact (hmin (abs_le.mp hx)).trans (Complex.re_le_norm _)

lemma bumpSchwartz_zero_of_abs_ge {x : ℝ} (hx : (1 : ℝ) / 8 ≤ |x|) :
    bumpSchwartz x = 0 := by
  simp only [bumpSchwartz_apply, Complex.ofReal_eq_zero]
  exact bump.zero_of_le_dist (by simpa [bump, Real.dist_eq] using hx)

def convolutionBump : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) bumpSchwartz bumpSchwartz

def psi : SchwartzMap ℝ ℂ := 𝓕 convolutionBump

lemma psi_apply (x : ℝ) : psi x = (𝓕 bumpSchwartz x) ^ 2 := by
  simp [psi, convolutionBump, SchwartzMap.fourier_convolution, pow_two]

lemma psi_im (x : ℝ) : (psi x).im = 0 := by
  simp only [psi_apply, pow_two, Complex.mul_im, bump_fourier_im, mul_zero, zero_mul, add_zero]

lemma psi_re (x : ℝ) : (psi x).re = (𝓕 bumpSchwartz x).re ^ 2 := by
  simp only [psi_apply, pow_two, Complex.mul_re, bump_fourier_im, mul_zero, sub_zero]

lemma psi_nonneg (x : ℝ) : 0 ≤ (psi x).re := by
  rw [psi_re]
  positivity

lemma psi_even (x : ℝ) : psi (-x) = psi x := by
  simp only [psi_apply, bump_fourier_even]

lemma psi_pos {x : ℝ} (hx : |x| ≤ 1) : 0 < (psi x).re := by
  rw [psi_re]
  exact sq_pos_of_pos (bump_fourier_re_pos hx)

theorem psi_uniform_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, |x| ≤ 1 → c ≤ (psi x).re := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-1 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    ((Complex.continuous_re.comp psi.continuous).continuousOn)
  exact ⟨(psi x₀).re, psi_pos (abs_le.mpr hx₀), fun x hx => hmin (abs_le.mp hx)⟩

lemma convolutionBump_zero_of_abs_ge {x : ℝ} (hx : (1 : ℝ) / 4 ≤ |x|) :
    convolutionBump x = 0 := by
  rw [convolutionBump, SchwartzMap.convolution_apply]
  by_contra h
  have hm : x ∈ Function.support (bumpSchwartz ⋆[ContinuousLinearMap.mul ℂ ℂ] bumpSchwartz) := h
  have hs := support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hm
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_add.mp hs
  have hu' : |u| < (1 : ℝ) / 8 := by
    by_contra hu'
    exact hu (bumpSchwartz_zero_of_abs_ge (le_of_not_gt hu'))
  have hv' : |v| < (1 : ℝ) / 8 := by
    by_contra hv'
    exact hv (bumpSchwartz_zero_of_abs_ge (le_of_not_gt hv'))
  have ha := abs_add_le u v
  rw [huv] at ha
  linarith

lemma fourier_twice (f : SchwartzMap ℝ ℂ) (x : ℝ) : 𝓕 (𝓕 f) x = f (-x) := by
  have h := congrArg (fun g : SchwartzMap ℝ ℂ => g (-x))
    (FourierTransform.fourierInv_fourier_eq (F := SchwartzMap ℝ ℂ) f)
  change 𝓕 (𝓕 f) (-(-x)) = f (-x) at h
  simpa only [neg_neg] using h

theorem fourier_psi_zero_of_abs_ge {ξ : ℝ} (hξ : (1 : ℝ) / 4 ≤ |ξ|) :
    𝓕 psi ξ = 0 := by
  rw [psi, fourier_twice]
  exact convolutionBump_zero_of_abs_ge (by simpa only [abs_neg] using hξ)

lemma hasCompactSupport_fourier_psi : HasCompactSupport ((𝓕 psi : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  apply HasCompactSupport.intro (K := Icc (-(1 : ℝ) / 4) (1 / 4)) isCompact_Icc
  intro ξ hξ
  apply fourier_psi_zero_of_abs_ge
  by_contra h
  apply hξ
  have hh := abs_le.mp (le_of_lt (lt_of_not_ge h))
  constructor <;> linarith [hh.1, hh.2]

lemma fourier_psi_at_zero : 𝓕 psi 0 = ∫ x : ℝ, psi x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp

lemma fourier_psi_at_zero_re_pos : 0 < (𝓕 psi 0).re := by
  rw [fourier_psi_at_zero]
  have hip : Integrable (psi : ℝ → ℂ) volume := psi.integrable
  have hre := integral_re hip
  change (∫ x : ℝ, (psi x).re) = (∫ x : ℝ, psi x).re at hre
  rw [← hre]
  apply integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp psi.continuous)
    (Complex.reCLM.integrable_comp hip) psi_nonneg
    (x := 0)
  exact ne_of_gt (psi_pos (by norm_num))

theorem exists_cutoff :
    ∃ ψ : SchwartzMap ℝ ℂ,
      (∀ x : ℝ, (ψ x).im = 0) ∧ (∀ x : ℝ, 0 ≤ (ψ x).re) ∧
      (∀ x : ℝ, ψ (-x) = ψ x) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, |x| ≤ 1 → c ≤ (ψ x).re) ∧
      (∀ ξ : ℝ, (1 : ℝ) / 4 ≤ |ξ| → 𝓕 ψ ξ = 0) :=
  ⟨psi, psi_im, psi_nonneg, psi_even, psi_uniform_lower, fun _ => fourier_psi_zero_of_abs_ge⟩

end Ostmann.SchwartzCutoff

end

end OAI
