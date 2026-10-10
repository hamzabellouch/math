import OAI.MeasureTheory.Falconer.Estimates.ScalarRegularizedGrowth

namespace OAI

/-! Explicit fixed-fold parameters for the nonporous binary construction.
 Their logarithmic branching approaches the original block width. -/
namespace Falconer

def scalarBinaryBranchCount (B C : ℕ) : ℕ := 2^(B-2*C)
def scalarBinaryCopyBound (B C : ℕ) : ℕ := 72*scalarBinaryBranchCount B C*2^C

theorem scalar_binary_parameter_contract {B C : ℕ} (hC : 7 ≤ C) (hBC : 2*C ≤ B) :
    (1/2:ℝ)^B*(1+2*(scalarBinaryBranchCount B C:ℝ)*(18*(2:ℝ)^C)) ≤ 1 := by
  have hcancel (n : ℕ) : (1/2:ℝ)^n*(2:ℝ)^n = 1 := by rw [← mul_pow]; norm_num
  have hsplit : (1/2:ℝ)^B = (1/2:ℝ)^(B-2*C)*(1/2:ℝ)^C*(1/2:ℝ)^C := by
    rw [← pow_add,← pow_add]
    congr 1
    omega
  have hprod : (1/2:ℝ)^B*(2:ℝ)^(B-2*C)*(2:ℝ)^C = (1/2:ℝ)^C := by
    calc
      _ = ((1/2:ℝ)^(B-2*C)*(2:ℝ)^(B-2*C))*
          ((1/2:ℝ)^C*(2:ℝ)^C)*(1/2:ℝ)^C := by rw [hsplit]; ring
      _ = _ := by rw [hcancel,hcancel]; ring
  have hbnd : (1/2:ℝ)^B ≤ 1/2 := by
    have hh : (1/2:ℝ)^B ≤ (1/2:ℝ)^1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (show 1 ≤ B by omega)
    simpa only [pow_one] using hh
  have hcbnd : (1/2:ℝ)^C ≤ 1/128 := by
    have hh := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1) hC
    norm_num at hh
    exact hh
  simp only [scalarBinaryBranchCount,Nat.cast_pow,Nat.cast_ofNat]
  have he : (1/2:ℝ)^B*(1+2*(2:ℝ)^(B-2*C)*(18*(2:ℝ)^C)) =
      (1/2:ℝ)^B+36*(1/2:ℝ)^C := by nlinarith [hprod]
  rw [he]
  linarith

theorem scalar_binary_parameter_copy_bound (B C : ℕ) :
    4*(scalarBinaryBranchCount B C:ℝ)*(18*(2:ℝ)^C) =
      (scalarBinaryCopyBound B C:ℝ) := by
  simp only [scalarBinaryCopyBound,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  ring

theorem scalar_binary_parameter_log {B C : ℕ} {κ : ℝ} (hBC : 2*C ≤ B)
    (hmargin : 8*(C:ℝ) ≤ κ*(B:ℝ)) :
    (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Real.log (scalarBinaryBranchCount B C+1:ℝ) := by
  have hp : 0 < (2:ℝ)^(B-2*C) := by positivity
  have hh := Real.log_le_log hp (show (2:ℝ)^(B-2*C) ≤ (2:ℝ)^(B-2*C)+1 by linarith)
  rw [Real.log_pow] at hh
  have hcast : ((B-2*C:ℕ):ℝ) = (B:ℝ)-2*(C:ℝ) := by
    rw [Nat.cast_sub hBC,Nat.cast_mul,Nat.cast_ofNat]
  rw [hcast] at hh
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hmargin hlog.le
  simp only [scalarBinaryBranchCount,Nat.cast_pow,Nat.cast_ofNat]
  nlinarith

end Falconer

end OAI
