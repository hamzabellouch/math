import Mathlib
import OAI.Combinatorics.UniformKServer.OfflineLaw

namespace OAI

noncomputable section
                                   
section

/-! An executable rational squared-binary-log slope with an absolute real
comparison coefficient. Its fixed integer multiplier is chosen once globally. -/
namespace UniformKServer.OffsetLP
open PartitionTree

def slope (mult k : ℕ) : ℚ := mult*(Nat.clog 2 (k+1))^2

theorem slope_nonneg (mult k : ℕ) : 0 ≤ slope mult k := by unfold slope;positivity

theorem slope_bounds (mult k : ℕ) (hk : 1 ≤ k) (hm : absoluteRate ≤ (mult : ℝ)) :
    absoluteRate*(Real.log (k+1))^2 ≤ (slope mult k : ℝ)  ∧ 
    (slope mult k : ℝ) ≤ (mult : ℝ)*(2/Real.log 2)^2*(Real.log (k+1))^2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk' : (2 : ℝ) ≤ k+1 := by exact_mod_cast (show 2 ≤ k+1 by omega)
  have hlog := Real.log_le_log (by norm_num : (0:ℝ) < 2) hk'
  have hn : 0 ≤ Real.log (k+1)/Real.log 2 := div_nonneg (htwo.le.trans hlog) htwo.le
  have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hceil : ⌈Real.log (k+1)/Real.log 2⌉₊=Nat.clog 2 (k+1) := by
    simpa only [Real.logb,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using
      Real.natCeil_logb_natCast 2 (k+1)
  have hlow := Nat.le_ceil (Real.log (k+1)/Real.log 2)
  have hupp := Nat.ceil_lt_add_one hn
  rw [hceil] at hlow hupp
  have h1 : 1 ≤ Real.log (k+1)/Real.log 2 := (le_div_iff₀ htwo).mpr (by simpa using hlog)
  have hclow : Real.log (k+1) ≤ (Nat.clog 2 (k+1) : ℝ) := by
    have hx : Real.log (k+1) ≤ Real.log (k+1)/Real.log 2 := by
      apply (le_div_iff₀ htwo).mpr
      exact mul_le_of_le_one_right (htwo.le.trans hlog) hl
    exact hx.trans hlow
  have hchi : (Nat.clog 2 (k+1) : ℝ) ≤ 2/Real.log 2*Real.log (k+1) := by
    calc
      _ ≤ 2*(Real.log (k+1)/Real.log 2) := by linarith
      _=_ := by ring
  have hsqlo : (Real.log (k+1))^2 ≤ (Nat.clog 2 (k+1) : ℝ)^2 := by nlinarith
  have hsqhi : (Nat.clog 2 (k+1) : ℝ)^2 ≤ (2/Real.log 2*Real.log (k+1))^2 := by nlinarith
  simp only [slope,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow]
  constructor
  · exact (mul_le_mul_of_nonneg_left hsqlo absoluteRate_nonneg).trans
      (mul_le_mul_of_nonneg_right hm (sq_nonneg _))
  · have hp := mul_le_mul_of_nonneg_left hsqhi (Nat.cast_nonneg mult : (0:ℝ) ≤ mult)
    nlinarith only [hp]

 theorem multiplier_exists :  ∃ mult : ℕ,0 < mult  ∧  absoluteRate ≤ (mult : ℝ) := by
  obtain ⟨m,hm⟩ := exists_nat_gt absoluteRate
  exact ⟨m+1,by omega,hm.le.trans (by exact_mod_cast (show m ≤ m+1 by omega))⟩
end UniformKServer.OffsetLP

end


end

end OAI
