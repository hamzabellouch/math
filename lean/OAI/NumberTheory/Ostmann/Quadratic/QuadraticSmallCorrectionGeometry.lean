import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelScale

namespace OAI

/-! # The small-kernel divisor cutoff gives the numerical matrix constraint -/

namespace Ostmann

theorem quadratic_small_correction_cutoff {M J : ℝ} {E B b D d : ℕ}
    (hM : 0 < M) (hJ : 1 ≤ J) (hE : 0 < E) (hB : 0 < B) (hD : 0 < D)
    (hb : B ≤ b) (hb' : b ≤ 2 * B) (hd : d ≤ 2 * D)
    (hcut : quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ)) :
    Real.sqrt M / (Real.sqrt B * D) ≤ 8 * E * J := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hbR : (B : ℝ) ≤ b := by exact_mod_cast hb
  have hbR' : (b : ℝ) ≤ 2 * B := by exact_mod_cast hb'
  have hdR : (d : ℝ) ≤ 2 * D := by exact_mod_cast hd
  have hJ₀ : 0 < J := zero_lt_one.trans_le hJ
  have hlo := (quadraticSmallScale_dyadic hM hBR hbR hbR').1
  unfold quadraticSecondLower at hcut
  have hh := (div_lt_iff₀ (show 0 < 2 * J by positivity)).mp hcut
  have hed : ((E * d : ℕ) : ℝ) ≤ (E : ℝ) * (2 * D) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hdR hER.le
  have heJ := mul_le_mul_of_nonneg_right hed (show 0 ≤ 2 * J by positivity)
  have hs : Real.sqrt (M / B) ≤ 8 * E * J * D := by nlinarith
  rw [Real.sqrt_div hM.le] at hs
  have hfin : (Real.sqrt M / Real.sqrt B) / D ≤ 8 * E * J :=
    (div_le_iff₀ hDR).mpr hs
  convert hfin using 1; ring

theorem quadratic_small_high_implies_lower {M J : ℝ} {b E d : ℕ}
    (hM : 0 < M) (hb : 0 < b) (hJ : 1 ≤ J)
    (hcut : quadraticSecondUpper (quadraticSmallScale M b) J < (E * d : ℕ)) :
    quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) := by
  have hx : 0 ≤ quadraticSmallScale M b := (quadraticSmallScale_pos hM hb).le
  have hJ₀ : 0 < J := zero_lt_one.trans_le hJ
  have hlow : quadraticSecondLower (quadraticSmallScale M b) J ≤ quadraticSmallScale M b := by
    unfold quadraticSecondLower
    exact div_le_self hx (by linarith)
  have hhigh : quadraticSmallScale M b ≤ quadraticSecondUpper (quadraticSmallScale M b) J := by
    unfold quadraticSecondUpper
    nlinarith
  exact hlow.trans_lt (hhigh.trans_lt hcut)

end Ostmann

end OAI
