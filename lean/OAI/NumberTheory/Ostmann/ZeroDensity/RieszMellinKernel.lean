import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic

namespace OAI

/-! # A single integral of the Chebyshev sum

The continuous weight max(1-u,0) has Mellin transform 1/(s(s+1)). This is the
one-sided smoothing needed to recover the sharp progression count.
-/

namespace Ostmann

open Complex MeasureTheory Set

noncomputable def rieszPrimeTest (u : ℝ) : ℂ := (max (1 - u) 0 : ℝ)

noncomputable def rieszMellinKernel (s : ℂ) : ℂ := 1 / (s * (s + 1))

theorem rieszPrimeTest_continuous : Continuous rieszPrimeTest := by
  unfold rieszPrimeTest
  fun_prop

theorem rieszPrimeTest_hasMellin (s : ℂ) (hs : 0 < s.re) :
    HasMellin rieszPrimeTest s (rieszMellinKernel s) := by
  let f : ℝ → ℂ := indicator (Ioc 0 1) (fun _ => 1)
  let g : ℝ → ℂ := indicator (Ioc 0 1) (fun u => (u : ℂ) ^ (1 : ℂ))
  have hf : HasMellin f s (1 / s) := hasMellin_one_Ioc hs
  have hg : HasMellin g s (1 / (s + 1)) :=
    hasMellin_cpow_Ioc 1 (by simpa using (show 0 < s.re + 1 by linarith))
  have hsub := hasMellin_sub hf.1 hg.1
  rw [hf.2, hg.2] at hsub
  have heq : EqOn (fun u => f u - g u) rieszPrimeTest (Ioi 0) := by
    intro u hu
    change 0 < u at hu
    by_cases hle : u ≤ 1
    · have hm : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, hle⟩
      simp [f, g, hm, rieszPrimeTest,
        max_eq_left (sub_nonneg.mpr hle), Complex.ofReal_sub]
    · have hn : u ∉ Ioc (0 : ℝ) 1 := fun h => hle h.2
      simp [f, g, indicator_of_notMem hn, rieszPrimeTest,
        max_eq_right (by linarith : 1 - u ≤ 0)]
  refine ⟨hsub.1.congr_fun (fun u hu =>
    congrArg (fun a : ℂ => (u : ℂ) ^ (s - 1) • a) (heq hu)) measurableSet_Ioi, ?_⟩
  have hi : mellin rieszPrimeTest s = mellin (fun u => f u - g u) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact congrArg (fun a : ℂ => (u : ℂ) ^ (s - 1) • a) (heq hu).symm
  rw [hi, hsub.2]
  have hsn : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith
  dsimp [rieszMellinKernel]
  field_simp
  ring

theorem rieszMellinKernel_line_bound (σ t : ℝ) (hσ : 1 ≤ σ) :
    ‖rieszMellinKernel ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      4 * (1 + |t|) ^ (-(2 : ℝ)) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have h1 : 1 ≤ ‖s‖ := by linarith [Complex.re_le_norm s]
  have h2 : 1 ≤ ‖s + 1‖ := by
    have hh := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re, hsre] at hh
    linarith
  have ht1 : |t| ≤ ‖s‖ := by simpa only [hsim] using Complex.abs_im_le_norm s
  have ht2 : |t| ≤ ‖s + 1‖ := by simpa [hsim] using Complex.abs_im_le_norm (s + 1)
  have ha : 0 < 1 + |t| := by positivity
  have hp : (1 + |t|) ^ 2 ≤ 4 * (‖s‖ * ‖s + 1‖) := by
    have hh := mul_le_mul (show 1 + |t| ≤ 2 * ‖s‖ by linarith)
      (show 1 + |t| ≤ 2 * ‖s + 1‖ by linarith) (by positivity) (by positivity)
    nlinarith
  change ‖1 / (s * (s + 1))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|),
    Real.rpow_two]
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖s‖ * ‖s + 1‖) (sq_pos_of_pos ha)).mpr
  nlinarith

end Ostmann

end OAI
