import OAI.NumberTheory.JointDickman.Analysis.CharacterRieszKernel

namespace OAI

/-! # The horizontal edges of the regular character contour -/
namespace JointDickman
open Complex Set

theorem characterRieszKernel_horizontal_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z L δ c T B ε : ℝ} {f : ℂ → ℂ}
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hB : 0 ≤ B) (hε : |ε| = 1)
    (hb : ∀ u ∈ Icc (-δ) c,
      ‖characterContourSeries χ z f (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I))‖ ≤ B) :
    ‖HIntegral (characterRieszKernel χ z L f) (-δ) c (ε*T)‖ ≤
      (5*B*Real.exp (L*c)/(1+T^2))*(δ+c) := by
  have hac : -δ ≤ c := by linarith
  unfold HIntegral
  have hbound : ‖∫ u in -δ..c,
      characterRieszKernel χ z L f ((u:ℂ)+((ε*T:ℝ):ℂ)*I)‖ ≤
      (5*B*Real.exp (L*c)/(1+T^2))*|c-(-δ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    have hu' : -δ ≤ u ∧ u ≤ c := by
      have hh : u ∈ Ioc (-δ) c := by simpa only [uIoc_of_le hac] using hu
      exact ⟨hh.1.le,hh.2⟩
    have hre : (((u:ℂ)+((ε*T:ℝ):ℂ)*I)).re = u := by simp
    have him : (((u:ℂ)+((ε*T:ℝ):ℂ)*I)).im^2 = T^2 := by
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
        mul_zero, zero_add, add_zero]
      have heps : ε^2 = 1 := by nlinarith [sq_abs ε]
      rw [mul_pow, heps, one_mul]
    have hs : 1/2 ≤ (1+((u:ℂ)+((ε*T:ℝ):ℂ)*I)).re := by
      simp only [add_re, one_re, hre]
      linarith [hu'.1]
    have hp := characterRieszKernel_point_bound χ (L := L) hB hs (hb u hu')
    rw [hre, him] at hp
    apply hp.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu'.2 hL)) (by positivity)
  rw [abs_of_nonneg (by linarith : 0 ≤ c-(-δ))] at hbound
  simpa only [sub_neg_eq_add, add_comm c δ] using hbound

end JointDickman

end OAI
