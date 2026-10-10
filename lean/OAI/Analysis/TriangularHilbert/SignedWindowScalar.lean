import OAI.Analysis.TriangularHilbert.GaussianMoments

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
noncomputable section

def oddWindow (s t : ℝ) : ℝ := t / Real.sqrt s * density s t

def windowRatio (s t : ℝ) : ℝ := oddWindow s t / density ((11/10)*s) t

lemma density_dilation {s q : ℝ} (hs : 0 < s) (hq : 0 < q) (t : ℝ) :
    density (q*s) t = (Real.sqrt s)⁻¹ * density q (t/Real.sqrt s) := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  have he : -(t/Real.sqrt s)^2/(2*q) = -t^2/(2*(q*s)) := by
    field_simp
    nlinarith [hsq]
  unfold density
  rw [show 2*Real.pi*(q*s)=s*(2*Real.pi*q) by ring,Real.sqrt_mul hs.le,he]
  simp only [mul_inv_rev]
  ring

lemma density_one_lambda (z : ℝ) :
    density 1 z = Real.sqrt (11/10) * Real.exp (-z^2/22) * density (11/10) z := by
  have hr : Real.sqrt (11/10) ≠ 0 := by positivity
  have hp : Real.sqrt (2*Real.pi) ≠ 0 := by positivity
  have hn : 2*Real.pi*(11/10) = (11/10)*(2*Real.pi) := by ring
  unfold density
  rw [hn,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 11/10)]
  simp only [mul_one,mul_inv_rev]
  have he : -z^2/22 + -z^2/(2*(11/10)) = -z^2/(2*1) := by ring
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-z^2/22 + -z^2/(2*(11/10))) := by rw [he]; simp
    _ = _ := by rw [Real.exp_add]; field_simp

lemma density_lambda_relation {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density s t = Real.sqrt (11/10) * Real.exp (-(t/Real.sqrt s)^2/22) * density ((11/10)*s) t := by
  have h1 := density_dilation hs (by norm_num : (0:ℝ)<1) t
  rw [one_mul] at h1
  rw [h1,density_dilation hs (by norm_num : (0:ℝ)<11/10),density_one_lambda]
  ring

lemma density_le_lambda {s : ℝ} (hs : 0 < s) (t : ℝ) :
    density s t ≤ Real.sqrt (11/10)*density ((11/10)*s) t := by
  rw [density_lambda_relation hs t]
  have he : Real.exp (-(t/Real.sqrt s)^2/22) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by norm_num))
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)) (density_nonneg (by positivity) t)

lemma windowRatio_eq {s : ℝ} (hs : 0 < s) (t : ℝ) :
    windowRatio s t = Real.sqrt (11/10)*(t/Real.sqrt s)*Real.exp (-(t/Real.sqrt s)^2/22) := by
  unfold windowRatio oddWindow
  rw [density_lambda_relation hs t]
  have hn : density ((11/10)*s) t ≠ 0 := (density_pos (by positivity) t).ne'
  rw [← mul_assoc, mul_div_cancel_right₀ _ hn]
  ring

lemma abs_mul_exp_square_le (z : ℝ) : |z| *Real.exp (-z^2/22) ≤ 22 := by
  have h := Real.add_one_le_exp (z^2/22)
  have hp := Real.exp_pos (-z^2/22)
  have ha : |z| ≤ 22*(z^2/22+1) := by nlinarith [sq_nonneg (|z|-1),sq_abs z]
  have he : Real.exp (z^2/22) * Real.exp (-z^2/22) = 1 := by rw [← Real.exp_add,show z^2/22 + -z^2/22 = 0 by ring,Real.exp_zero]
  have hb := mul_le_mul_of_nonneg_right h hp.le
  rw [he] at hb
  have hc := mul_le_mul_of_nonneg_right ha hp.le
  nlinarith

lemma abs_windowRatio_le {s : ℝ} (hs : 0 < s) (t : ℝ) : |windowRatio s t| ≤ 44 := by
  rw [windowRatio_eq hs t,abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos (Real.exp_pos _)]
  have h := abs_mul_exp_square_le (t/Real.sqrt s)
  have hr : Real.sqrt (11/10) ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
  have hn := Real.sqrt_nonneg (11/10)
  nlinarith

lemma oddWindow_score {s : ℝ} (hs : 0 < s) (u p : ℝ) :
    oddWindow s (u-p) = Real.sqrt s*score u p s*density s (u-p) := by
  have hr : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  unfold oddWindow score
  congr 1
  field_simp
  rw [hsq]

end
end TriangularHilbert.Heat
end

end OAI
