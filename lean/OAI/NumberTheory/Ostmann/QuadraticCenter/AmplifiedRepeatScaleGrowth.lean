import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedRepeatScalesBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter

theorem amplifiedRepeatTau_sq {Z K k : ℕ} (hZ : 0 < (Z : ℝ)) :
    amplifiedRepeatTau Z K k ^ 2 =
      Real.exp ((2 / 125 : ℝ) * K / k) / Z := by
  unfold amplifiedRepeatTau
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-Real.log Z / 2 + (1 / 125 : ℝ) * K / k) =
    -Real.log Z + (2 / 125 : ℝ) * K / k by ring]
  rw [Real.exp_add, Real.exp_neg, Real.exp_log hZ]
  ring

theorem amplifiedRepeatTau_scale {T c J : ℝ} {Z K k : ℕ}
    (hT : 2 ≤ T) (hc : 0 < c) (hZ : 0 < Real.log Z)
    (hZupper : Real.log Z ≤ T ^ 2) (hk : 0 < k) (hkT : (k : ℝ) ≤ T)
    (hcost : (k : ℝ) * Real.log T ≤ (1 / 500 : ℝ) * K)
    (hcT : 256 ≤ c * T ^ 2) (hJ : c * (Z : ℝ) / Real.log Z ≤ J) :
    4 * ((k : ℝ) + 1) ^ 2 ≤ Real.sqrt J * amplifiedRepeatTau Z K k := by
  have hTpos : 0 < T := by linarith
  have hZpos : 0 < (Z : ℝ) := by
    have := (Real.log_pos_iff (Nat.cast_nonneg Z)).mp hZ
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hJpos : 0 < J := (div_pos (mul_pos hc hZpos) hZ).trans_le hJ
  have hgain : T ^ 8 ≤ Real.exp ((2 / 125 : ℝ) * K / k) := by
    have hexp : 8 * Real.log T ≤ (2 / 125 : ℝ) * K / k := by
      apply (le_div_iff₀ hkpos).mpr
      nlinarith
    calc
      T ^ 8 = Real.exp (8 * Real.log T) := by
        simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using
          (Real.exp_nat_mul (Real.log T) 8).symm
      _ ≤ _ := Real.exp_le_exp.mpr hexp
  have hlarge : 256 * T ^ 4 * Real.log Z ≤ c * T ^ 8 := by
    calc
      _ ≤ 256 * T ^ 4 * T ^ 2 :=
        mul_le_mul_of_nonneg_left hZupper (by positivity)
      _ = 256 * T ^ 6 := by ring
      _ ≤ (c * T ^ 2) * T ^ 6 :=
        mul_le_mul_of_nonneg_right hcT (by positivity)
      _ = c * T ^ 8 := by ring
  have hscaleSq : 16 * ((k : ℝ) + 1) ^ 4 ≤
      J * amplifiedRepeatTau Z K k ^ 2 := by
    calc
      _ ≤ 256 * T ^ 4 := by
        have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
          (show (k : ℝ) + 1 ≤ 2 * T by linarith) 4
        nlinarith
      _ ≤ c * T ^ 8 / Real.log Z := (le_div_iff₀ hZ).mpr hlarge
      _ ≤ c * Real.exp ((2 / 125 : ℝ) * K / k) / Real.log Z :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgain hc.le) hZ.le
      _ = (c * (Z : ℝ) / Real.log Z) * amplifiedRepeatTau Z K k ^ 2 := by
        rw [amplifiedRepeatTau_sq hZpos]
        field_simp
      _ ≤ J * amplifiedRepeatTau Z K k ^ 2 :=
        mul_le_mul_of_nonneg_right hJ (sq_nonneg _)
  have hsqrt := Real.sq_sqrt hJpos.le
  have hτ := amplifiedRepeatTau_pos Z K k
  have hnonneg : 0 ≤ Real.sqrt J * amplifiedRepeatTau Z K k := by positivity
  have hid : (Real.sqrt J * amplifiedRepeatTau Z K k) ^ 2 =
      J * amplifiedRepeatTau Z K k ^ 2 := by rw [mul_pow, hsqrt]
  nlinarith [sq_nonneg (4 * ((k : ℝ) + 1) ^ 2 -
    Real.sqrt J * amplifiedRepeatTau Z K k)]

end Ostmann.QuadraticCenter

end

end OAI
