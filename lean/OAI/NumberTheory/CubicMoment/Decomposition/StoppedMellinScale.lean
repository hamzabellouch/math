import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorGeometry

namespace OAI

/-! Rounding the coefficient length in the ordinary mean introduces only
fixed factors. Its logarithmic cutoff remains a fixed power of log X. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_mellin_ceil_scale {X b κ : ℝ} (hX : Real.exp 1 ≤ X)
    (hκ : 0 < κ) (hb : X^κ ≤ b) (hbX : b ≤ X) :
    1 ≤ b ∧ b ≤ (⌈b⌉₊:ℝ) ∧ (⌈b⌉₊:ℝ) ≤ 2*b ∧
      κ*Real.log X ≤ 1+Real.log (⌈b⌉₊:ℝ) ∧
      1+Real.log (⌈b⌉₊:ℝ) ≤ 3*Real.log X := by
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hb1 : 1 ≤ b := (Real.one_le_rpow hX1 hκ.le).trans hb
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hbceil : b ≤ (⌈b⌉₊:ℝ) := Nat.le_ceil b
  have hceil : (⌈b⌉₊:ℝ) ≤ 2*b := by linarith [Nat.ceil_lt_add_one hbp.le]
  have hceilX : (⌈b⌉₊:ℝ) ≤ 2*X := hceil.trans (by linarith)
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlow := Real.log_le_log (Real.rpow_pos_of_pos hXp κ) (hb.trans hbceil)
  rw [Real.log_rpow hXp] at hlow
  have hhigh := Real.log_le_log (hbp.trans_le hbceil) hceilX
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hXp.ne'] at hhigh
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  refine ⟨hb1,hbceil,hceil,by linarith,by linarith⟩

lemma stopped_mellin_cutoff_scale {L A : ℝ} (hL : 1 ≤ L) (n : ℕ)
    (hA : 0 ≤ A) (hAL : A ≤ 3*L) (hLn : (3:ℝ)^n ≤ L) :
    A^n ≤ L^(n+1) := by
  calc
    _ ≤ (3*L)^n := pow_le_pow_left₀ hA hAL _
    _ = (3:ℝ)^n*L^n := mul_pow _ _ _
    _ ≤ L*L^n := mul_le_mul_of_nonneg_right hLn (pow_nonneg (zero_le_one.trans hL) _)
    _ = _ := by rw [pow_succ]; ring

lemma stopped_mellin_mass_scale {b N L A κ : ℝ} (_hb : 0 ≤ b) (hL : 0 < L)
    (hκ : 0 < κ) (hN : 0 ≤ N) (hNb : N ≤ 2*b) (hA : κ*L ≤ A) (k : ℕ) :
    N^2/A^k ≤ (4/κ^k)*b^2/L^k := by
  have hAp : 0 < A := (mul_pos hκ hL).trans_le hA
  have hden := pow_le_pow_left₀ (mul_nonneg hκ.le hL.le) hA k
  rw [mul_pow] at hden
  calc
    _ ≤ (2*b)^2/(κ^k*L^k) :=
      div_le_div₀ (sq_nonneg (2*b)) (pow_le_pow_left₀ hN hNb 2) (by positivity) hden
    _ = _ := by field_simp; ring

end CubicFirstMoment

end

end OAI
