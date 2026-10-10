import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply

def supplyEpsilon : ℝ := 1/1000000

theorem supplyEpsilon_pos : 0 < supplyEpsilon := by norm_num [supplyEpsilon]
theorem supplyEpsilon_le_one : supplyEpsilon  ≤  1 := by norm_num [supplyEpsilon]

theorem local_error_square {P : ℝ} (hP : 0<P) :
    100*(8*supplyEpsilon/Real.sqrt P)^2 = 6400*supplyEpsilon^2/P := by
  have hr := (Real.sqrt_pos.mpr hP).ne'
  have hs := Real.sq_sqrt hP.le
  field_simp
  rw [hs]
  ring

theorem local_error_small {P : ℝ} (hP : 1000 ≤ P) :
    0  ≤  8*supplyEpsilon/Real.sqrt P ∧ 8*supplyEpsilon/Real.sqrt P  ≤  1/100 := by
  have hP0 : 0<P := by linarith
  have hr : 1 ≤ Real.sqrt P := by
    have hs := Real.sq_sqrt hP0.le
    nlinarith [Real.sqrt_nonneg P]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) supplyEpsilon_pos.le) (Real.sqrt_nonneg _)
  · apply (div_le_iff₀ (Real.sqrt_pos.mpr hP0)).mpr
    norm_num only [supplyEpsilon] at ⊢
    linarith

theorem scalar_near_one {P s : ℝ} (hP : 1000 ≤ P)
    (hlo : 1-(2+8*supplyEpsilon)/P  ≤  s)
    (hhi : s  ≤  1+(2+8*supplyEpsilon)/P) :
    98/100 ≤ s ∧ s ≤ 102/100 := by
  have hP0 : 0<P := by linarith
  have hsmall : (2+8*supplyEpsilon)/P  ≤  2/100 := by
    apply (div_le_iff₀ hP0).mpr
    norm_num [supplyEpsilon] at *
    linarith
  constructor <;> linarith

theorem local_uniform_norm_numerical {P s N : ℝ} (hP : 1000 ≤ P)
    (hs : s  ≤  1+(2+8*supplyEpsilon)/P)
    (hN : N  ≤  s+100*(8*supplyEpsilon/Real.sqrt P)^2) : N ≤ 1+3/P := by
  have hP0 : 0<P := by linarith
  rw [local_error_square hP0] at hN
  have hc : 2+8*supplyEpsilon+6400*supplyEpsilon^2  ≤  3 := by norm_num [supplyEpsilon]
  have hh := div_le_div_of_nonneg_right hc hP0.le
  rw [add_div,add_div] at hh
  rw [add_div] at hs
  linarith

theorem local_strict_norm_numerical {P s N : ℝ} (hP : 1000 ≤ P)
    (hs : s ≤ 1-((17/10:ℝ)*(1-supplyEpsilon^2)-4*supplyEpsilon)/P)
    (hN : N ≤ s+100*(8*supplyEpsilon/Real.sqrt P)^2) :
    N ≤ 1-(33/20:ℝ)/P := by
  have hP0 : 0<P := by linarith
  rw [local_error_square hP0] at hN
  have hc : (33/20:ℝ)+6400*supplyEpsilon^2  ≤ 
      (17/10:ℝ)*(1-supplyEpsilon^2)-4*supplyEpsilon := by norm_num [supplyEpsilon]
  have hh := div_le_div_of_nonneg_right hc hP0.le
  rw [add_div] at hh
  linarith

theorem local_relative_norm_numerical {P N U : ℝ} (hP : 1000 ≤ P)
    (hN : N ≤ 1-(33/20:ℝ)/P) (hU : 1-4*supplyEpsilon/P ≤ U) :
    N ≤ U*(1-(8/5:ℝ)/P) := by
  have hP0 : 0<P := by linarith
  have hscale : 0 ≤ 1-(8/5:ℝ)/P := by
    have h := (div_le_iff₀ hP0).mpr (show (8/5:ℝ) ≤ 1*P by linarith)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hU hscale
  have he : 1-(33/20:ℝ)/P  ≤  (1-4*supplyEpsilon/P)*(1-(8/5:ℝ)/P) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hP0)).mp
    field_simp
    norm_num [supplyEpsilon]
    nlinarith
  exact hN.trans (he.trans hmul)

end Ostmann.Supply

end

end OAI
