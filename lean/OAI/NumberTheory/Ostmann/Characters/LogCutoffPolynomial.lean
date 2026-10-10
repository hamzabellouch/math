import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPolynomialWeight

namespace OAI

/-! # Polynomial factors for the actual logarithmic node cutoff -/

namespace Ostmann

private theorem log_lipschitz_on_positive_ray (a x y : ℝ) (ha : 0 < a)
    (hx : a ≤ x) (hy : a ≤ y) : |Real.log x - Real.log y| ≤ a⁻¹ * |x - y| := by
  have hordered (x y : ℝ) (hx : a ≤ x) (hxy : x ≤ y) :
      |Real.log x - Real.log y| ≤ a⁻¹ * |x - y| := by
    have hx0 : 0 < x := ha.trans_le hx
    have hy0 : 0 < y := hx0.trans_le hxy
    have hl := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hx0)] at hl
    have he : y / x - 1 = (y - x) * x⁻¹ := by field_simp
    rw [he] at hl
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx0 hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    calc
      _ = Real.log y - Real.log x := by ring
      _ ≤ (y - x) * x⁻¹ := hl
      _ ≤ (y - x) * a⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ ha hx) (sub_nonneg.mpr hxy)
      _ = _ := by ring
  rcases le_total x y with hxy | hyx
  · exact hordered x y hx hxy
  · simpa only [abs_sub_comm] using hordered y x hy hyx

noncomputable def positiveLogCutoff (φ : ℝ → ℝ) (G x : ℝ) : ℝ :=
  if 0 < x then φ (Real.log x - G) else 0

/-- The center appears in the lower endpoint and its reciprocal Lipschitz
constant. These cancel in the total variation budget. -/
noncomputable def logCutoffPolynomialFactor (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    ClippedPolynomialFactor where
  polynomial := P
  profile x := (φ (Real.log x - G) : ℂ)
  lo := Real.exp (G - 1)
  hi := Real.exp (G + 1)
  bound := B
  lip := D * (Real.exp (G - 1))⁻¹
  lo_le_hi := Real.exp_le_exp.mpr (by linarith)
  bound_nonneg := hB
  lip_nonneg := mul_nonneg hD (inv_nonneg.mpr (Real.exp_pos _).le)
  norm_le x _ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hφ (Real.log x - G)
  lipschitz x hx y hy := by
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ D * |(Real.log x - G) - (Real.log y - G)| := hlip _ _
      _ = D * |Real.log x - Real.log y| := by congr 2; ring
      _ ≤ D * ((Real.exp (G - 1))⁻¹ * |x - y|) :=
        mul_le_mul_of_nonneg_left (log_lipschitz_on_positive_ray _ x y (Real.exp_pos _) hx.1 hy.1) hD
      _ = _ := by ring

/-- Clipping changes no node factor, including nonpositive inserted values
and both boundary points of the compact logarithmic cutoff. -/
theorem logCutoffPolynomialFactor_value (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (z : ℝ) :
    (logCutoffPolynomialFactor P φ G B D hB hD hφ hlip).value z =
      (positiveLogCutoff φ G (P.eval z) : ℂ) := by
  let x := P.eval z
  have hlow : φ (Real.log (Real.exp (G - 1)) - G) = 0 := by
    rw [Real.log_exp]
    apply hout
    norm_num
  have hhigh : φ (Real.log (Real.exp (G + 1)) - G) = 0 := by
    rw [Real.log_exp]
    apply hout
    norm_num
  by_cases hxlo : x < Real.exp (G - 1)
  · have he : clipRealInterval (Real.exp (G - 1)) (Real.exp (G + 1)) x = Real.exp (G - 1) := by
      simp only [clipRealInterval, max_eq_left (le_trans (min_le_right _ _) hxlo.le)]
    change (φ (Real.log (clipRealInterval (Real.exp (G - 1)) (Real.exp (G + 1)) x) - G) : ℂ) = (positiveLogCutoff φ G x : ℂ)
    rw [he, hlow]
    by_cases hx0 : 0 < x
    · have hlog : Real.log x < G - 1 := (Real.log_lt_iff_lt_exp hx0).mpr hxlo
      have hz : φ (Real.log x - G) = 0 := hout _ (by rw [abs_of_neg (by linarith)]; linarith)
      simp only [positiveLogCutoff, ite_eq_left hx0, hz, Complex.ofReal_zero]
    · simp only [positiveLogCutoff, ite_eq_right hx0, Complex.ofReal_zero]
  · have hxlo' : Real.exp (G - 1) ≤ x := le_of_not_gt hxlo
    have hx0 : 0 < x := (Real.exp_pos _).trans_le hxlo'
    by_cases hxhi : Real.exp (G + 1) < x
    · have he : clipRealInterval (Real.exp (G - 1)) (Real.exp (G + 1)) x = Real.exp (G + 1) := by
        simp only [clipRealInterval, min_eq_left hxhi.le,
          max_eq_right (Real.exp_le_exp.mpr (by linarith : G - 1 ≤ G + 1))]
      change (φ (Real.log (clipRealInterval (Real.exp (G - 1)) (Real.exp (G + 1)) x) - G) : ℂ) = (positiveLogCutoff φ G x : ℂ)
      rw [he, hhigh]
      have hlog : G + 1 < Real.log x := (Real.lt_log_iff_exp_lt hx0).mpr hxhi
      have hz : φ (Real.log x - G) = 0 := hout _ (by rw [abs_of_pos (by linarith)]; linarith)
      simp only [positiveLogCutoff, ite_eq_left hx0, hz, Complex.ofReal_zero]
    · rw [ClippedPolynomialFactor.value_of_mem _ z ⟨hxlo', le_of_not_gt hxhi⟩]
      simp only [logCutoffPolynomialFactor, positiveLogCutoff, x, ite_eq_left hx0]

/-- No large-center cost occurs in a logarithmic node cutoff's variation. -/
theorem logCutoffPolynomialFactor_budget (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    let f := logCutoffPolynomialFactor P φ G B D hB hD hφ hlip
    2 * f.bound + f.lip * (f.hi - f.lo) = 2 * B + D * (Real.exp 2 - 1) := by
  change 2 * B + (D * (Real.exp (G - 1))⁻¹) * (Real.exp (G + 1) - Real.exp (G - 1)) = _
  rw [show G + 1 = (G - 1) + 2 by ring, Real.exp_add]
  field_simp

end Ostmann

end OAI
