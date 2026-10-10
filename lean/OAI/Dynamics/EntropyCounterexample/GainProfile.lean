import Mathlib

namespace OAI

noncomputable section

namespace Problem340

def gainBump : ContDiffBump (51 : ℝ) where
  rIn := 44
  rOut := 89 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def gainProfile (L : ℝ) (t : ℝ) : ℝ := L * gainBump t

lemma gainProfile_contDiff (L : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gainProfile L) :=
  contDiff_const.mul gainBump.contDiff

lemma gainProfile_mem_Icc {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    gainProfile L t ∈ Set.Icc (0 : ℝ) L := by
  constructor
  · exact mul_nonneg hL gainBump.nonneg
  · simpa only [gainProfile, mul_one] using mul_le_mul_of_nonneg_left (gainBump.le_one (x := t)) hL

lemma gainProfile_zero_outside {L t : ℝ} (ht : t ∉ Set.Ioo (6 : ℝ) 96) :
    gainProfile L t = 0 := by
  have hb : gainBump t = 0 := by
    apply gainBump.zero_of_le_dist
    rw [Real.dist_eq]
    change (89 / 2 : ℝ) ≤ |t - 51|
    simp only [Set.mem_Ioo, not_and_or, not_lt] at ht
    rcases ht with ht | ht
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_of_nonneg (by linarith)]
      linarith
  simp [gainProfile, hb]

lemma gainProfile_eq_gain (L : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (7 : ℝ) 90) :
    gainProfile L t = L := by
  have hb : gainBump t = 1 := by
    apply gainBump.one_of_mem_closedBall
    rw [Real.closedBall_eq_Icc]
    norm_num [gainBump]
    constructor <;> linarith [ht.1, ht.2]
  simp [gainProfile, hb]

lemma gainProfile_eq_zero (L : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (2 : ℝ) 5) :
    gainProfile L t = 0 := by
  have hb : gainBump t = 0 := by
    apply gainBump.zero_of_le_dist
    rw [Real.dist_eq]
    change (89 / 2 : ℝ) ≤ |t - 51|
    rw [abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.2]
  simp [gainProfile, hb]

end Problem340

end

end OAI
