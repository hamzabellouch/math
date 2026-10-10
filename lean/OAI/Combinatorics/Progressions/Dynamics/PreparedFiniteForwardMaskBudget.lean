import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_two_shiftedPowers_le_work
    (A C : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : C + 1 ≤ A) (hx : 0 ≤ x) :
    2 * (preparedFiniteForwardParameter A stageCountConstant n x + C) ^ C ≤
      preparedFiniteForwardWork A stageCountConstant n x := by
  let b := preparedFiniteForwardParameter A stageCountConstant n x
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hC' : (C : ℝ) ≤ A := Nat.cast_le.mpr (Nat.le_trans (Nat.le_succ C) hC)
  have hA' : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbase : 2 ≤ b + A := by linarith only [hb, hA']
  have hpow : (b + C) ^ C ≤ (b + A) ^ C :=
    pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg C)) (add_le_add (le_refl b) hC') C
  rw [preparedFiniteForwardWork_eq]
  change 2 * (b + C) ^ C ≤ (b + A) ^ A
  calc
    2 * (b + C) ^ C ≤ 2 * (b + A) ^ C := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ (b + A) ^ C * (b + A) := by
      have hpow0 : 0 ≤ (b + (A : ℝ)) ^ C := pow_nonneg (by linarith only [hbase]) C
      have hmul : 0 ≤ (b + (A : ℝ)) ^ C * (b + A - 2) :=
        mul_nonneg hpow0 (by linarith only [hbase])
      nlinarith only [hmul]
    _ = (b + A) ^ (C + 1) := (pow_succ _ _).symm
    _ ≤ (b + A) ^ A := pow_le_pow_right₀ (by linarith only [hbase]) hC

theorem preparedFiniteForward_masked_error_budget
    (A C : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog maskLog Eres : ℝ}
    (hA : 2 ≤ A) (hC : C + 1 ≤ A) (hx : 0 ≤ x)
    (hmask : maskLog ≤ (preparedFiniteForwardParameter A stageCountConstant n x + C) ^ C)
    (herror : Eres ≤ (preparedFiniteForwardParameter A stageCountConstant n x + C) ^ C) :
    (preparedFiniteForwardPrefixLog A stageCountConstant n x + maskLog) +
      gainLog + Eres + stageLog + 6 ≤
        preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog := by
  have hwork := preparedFiniteForward_two_shiftedPowers_le_work A C stageCountConstant n hA hC hx
  unfold preparedFiniteForwardModelPrecision
  linarith only [hmask, herror, hwork]

end Erdos3.VectorPolynomial

end

end OAI
