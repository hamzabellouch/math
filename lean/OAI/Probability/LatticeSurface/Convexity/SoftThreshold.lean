import Mathlib

namespace OAI

namespace SparseHoles

noncomputable def softThreshold (M t : ℝ) : ℝ := Real.sign t * max (|t|-M) 0

lemma softThreshold_eq (M t : ℝ) (hM : 0≤M) :
    softThreshold M t = max (t-M) 0 - max (-t-M) 0 := by
  rcases lt_trichotomy t 0 with h|h|h
  · simp only [softThreshold,Real.sign_of_neg h,abs_of_neg h]
    rw [max_eq_right (by linarith : t-M≤0)]
    ring
  · subst t;simp [softThreshold,max_eq_right (neg_nonpos.mpr hM)]
  · simp only [softThreshold,Real.sign_of_pos h,abs_of_pos h]
    rw [max_eq_right (by linarith : -t-M≤0)]
    ring

lemma softThreshold_lipschitz (M x y : ℝ) (hM : 0≤M) :
    |softThreshold M y-softThreshold M x| ≤ |y-x| := by
  rw [softThreshold_eq M y hM,softThreshold_eq M x hM]
  simp only [max_def,abs_le]
  split_ifs <;> constructor <;> linarith [le_abs_self (y-x),neg_le_abs (y-x)]

lemma softThreshold_error (M x : ℝ) (hM : 0≤M) :
    |x-softThreshold M x|≤M := by
  rw [softThreshold_eq M x hM]
  simp only [max_def,abs_le]
  split_ifs <;> constructor <;> linarith

lemma softThreshold_zero (M : ℝ) (hM : 0≤M) : softThreshold M 0=0 := by
  rw [softThreshold_eq M 0 hM];simp

end SparseHoles

end OAI
