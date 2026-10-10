import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticLower
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! An effective disk about one for a real quadratic character. The
radius is polynomial in the modulus and does not use an exceptional-zero input. -/

namespace TwoPointCorrelations

open Complex Metric
open scoped Classical

lemma mrt_character_LFunction_deriv_local {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : ‖s - 1‖ ≤ (1 / 4 : ℝ)) :
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ 12 * q := by
  have hd := (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
    (s := ball s (1 / 4))
  have hb : ∀ z ∈ sphere s (1 / 4 : ℝ), ‖DirichletCharacter.LFunction χ z‖ ≤ 3 * q := by
    intro z hz
    have hzdist : ‖z - s‖ = (1 / 4 : ℝ) := by simpa only [mem_sphere_iff_norm] using hz
    have hz1 : ‖z - 1‖ ≤ (1 / 2 : ℝ) := by
      have hh := norm_sub_le_norm_sub_add_norm_sub z s (1 : ℂ)
      linarith
    have hr : (1 / 2 : ℝ) ≤ z.re := by
      have hh := (Complex.abs_re_le_norm (z - 1)).trans hz1
      rw [Complex.sub_re, Complex.one_re] at hh
      linarith [(abs_le.mp hh).1]
    have hn : ‖z‖ ≤ (3 / 2 : ℝ) := by
      have hh := norm_sub_le_norm_sub_add_norm_sub z (1 : ℂ) 0
      simp only [sub_zero, norm_one] at hh
      linarith
    exact (mrt_character_LFunction_norm_halfPlane χ hχ hr).trans (by
      have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (2 * q : ℝ))
      nlinarith)
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) hd hb
  norm_num at hh ⊢
  linarith

lemma mrt_character_LFunction_local_difference {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : ‖s - 1‖ ≤ (1 / 4 : ℝ)) :
    ‖DirichletCharacter.LFunction χ s - DirichletCharacter.LFunction χ 1‖ ≤
      (12 * q : ℝ) * ‖s - 1‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (s := closedBall (1 : ℂ) (1 / 4))
    (fun z _ => DirichletCharacter.differentiable_LFunction hχ z)
    (fun z hz => mrt_character_LFunction_deriv_local χ hχ
      (by simpa only [mem_closedBall_iff_norm] using hz))
    (convex_closedBall (1 : ℂ) (1 / 4))
  · exact mem_closedBall_self (by norm_num)
  · simpa only [mem_closedBall_iff_norm] using hs

theorem mrt_quadratic_near_one_nonzero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / (1536 * (q : ℝ) ^ 2)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hr : 1 / (1536 * (q : ℝ) ^ 2) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 1536 * (q : ℝ) ^ 2)).mpr
    nlinarith
  have hh := mrt_character_LFunction_local_difference χ hχ (hs.trans hr)
  have hl := mrt_quadratic_LFunction_one_lower χ hχ hsq
  intro hz
  rw [hz, zero_sub, norm_neg] at hh
  have hu := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (12 * q : ℝ))
  have he : (12 * q : ℝ) * (1 / (1536 * (q : ℝ) ^ 2)) = 1 / (128 * q) := by
    field_simp
    ring
  rw [he] at hu
  have hlt : 1 / (128 * (q : ℝ)) < 1 / (64 * (q : ℝ)) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith
  exact (not_lt_of_ge (hl.trans (hh.trans hu))) hlt

end TwoPointCorrelations

end OAI
