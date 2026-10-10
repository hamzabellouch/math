import OAI.Analysis.LipschitzHilbert.Phase.FourthMoment
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-!
# A positive averaging kernel with compact Fourier support

Square the norm of the Fourier transform of a smooth compactly supported
bump. Plancherel converts its Fourier moments into overlaps of translates
of the bump; disjoint supports therefore give exact annihilation.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform ComplexInnerProductSpace

namespace LipschitzHilbert

open PhaseCombinatorics

/-- The nonnegative physical-space averaging density before normalization. -/
def fourierSquare (h : SchwartzMap ℝ ℂ) (t : ℝ) : ℝ := ‖𝓕 h t‖ ^ 2

theorem schwartz_norm_sq_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun t => ‖h t‖ ^ 2) := by
  have hbound (t : ℝ) : ‖h t‖ ^ 2 ≤ SchwartzMap.seminorm ℝ 0 0 h * ‖h t‖ := by
    nlinarith [mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ h t) (norm_nonneg (h t))]
  exact (h.integrable.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 h)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h t‖)] using hbound t)

theorem fourierSquare_integrable (h : SchwartzMap ℝ ℂ) : Integrable (fourierSquare h) :=
  schwartz_norm_sq_integrable (𝓕 h)

theorem fourierSquare_nonneg (h : SchwartzMap ℝ ℂ) (t : ℝ) : 0 ≤ fourierSquare h t := sq_nonneg _

theorem fourierSquare_continuous (h : SchwartzMap ℝ ℂ) : Continuous (fourierSquare h) := by
  exact (𝓕 h).continuous.norm.pow 2

/-- Translation on the compact-frequency side becomes a unit phase. -/
theorem schwartz_fourier_translate (h : SchwartzMap ℝ ℂ) (a x : ℝ) :
    𝓕 (h.compSubConstCLM ℂ (-a)) x = character (2 * Real.pi * a) x * 𝓕 h x := by
  have ht := congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure ℝ) (h : ℝ → ℂ) a) x
  have hphase : (Real.fourierChar (a * x) : ℂ) = character (2 * Real.pi * a) x := by
    simp only [Real.fourierChar_apply, character]
    congr 1
    push_cast
    ring
  simpa only [SchwartzMap.fourier_coe, Real.fourier_real_eq,
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, Function.comp_apply,
    Fourier.fourierIntegral_def, Circle.smul_def, smul_eq_mul, hphase] using ht

/-- The Fourier moment of the square is an overlap integral of the bump and
its translate. This is the exact support calculation needed for averaging. -/
theorem fourierSquare_moment (h : SchwartzMap ℝ ℂ) (a : ℝ) :
    (∫ t, (fourierSquare h t : ℂ) * character (2 * Real.pi * a) t) =
      ∫ x, inner ℂ (h x) (h (x + a)) := by
  have hplan := SchwartzMap.integral_inner_fourier_fourier h (h.compSubConstCLM ℂ (-a))
  have hpoint (t : ℝ) :
      inner ℂ (𝓕 h t) (𝓕 (h.compSubConstCLM ℂ (-a)) t) =
        (fourierSquare h t : ℂ) * character (2 * Real.pi * a) t := by
    rw [schwartz_fourier_translate]
    change inner ℂ (𝓕 h t) (character (2 * Real.pi * a) t • 𝓕 h t) = _
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    unfold fourierSquare
    push_cast
    exact mul_comm _ _
  simpa only [hpoint, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] using hplan

/-- A bump supported in `(-r,r)` produces no moment at translation distances
at least `2r`, including the support endpoints. -/
theorem fourierSquare_moment_eq_zero (h : SchwartzMap ℝ ℂ) {r a : ℝ}
    (hsupport : ∀ x, r ≤ |x| → h x = 0) (ha : 2 * r ≤ |a|) :
    (∫ t, (fourierSquare h t : ℂ) * character (2 * Real.pi * a) t) = 0 := by
  rw [fourierSquare_moment]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  change inner ℂ (h x) (h (x + a)) = 0
  by_cases hx : r ≤ |x|
  · rw [hsupport x hx, inner_zero_left]
  · have hxa : r ≤ |x + a| := by
      have htri : |a| ≤ |x + a| + |x| := by
        have h := abs_sub (x + a) x
        simpa only [add_sub_cancel_left] using h
      linarith [lt_of_not_ge hx]
    rw [hsupport (x + a) hxa, inner_zero_right]

/-- The total mass is positive whenever the original bump is nonzero at one
point, and agrees with its squared L2 norm by Plancherel. -/
theorem fourierSquare_mass_pos (h : SchwartzMap ℝ ℂ) {x : ℝ} (hx : h x ≠ 0) :
    0 < ∫ t, fourierSquare h t := by
  change 0 < ∫ t, ‖𝓕 h t‖ ^ 2
  rw [SchwartzMap.integral_norm_sq_fourier]
  exact integral_pos_of_integrable_nonneg_nonzero (h.continuous.norm.pow 2)
    (schwartz_norm_sq_integrable h) (fun _ => sq_nonneg _)
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

end LipschitzHilbert

end

end OAI
