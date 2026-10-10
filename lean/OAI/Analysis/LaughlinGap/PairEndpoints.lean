import Mathlib
import OAI.Analysis.LaughlinGap.SpectralBound

namespace OAI

/-! Pair Endpoints. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma pairCoefficient_one {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    pairCoefficient Q z ⟨1,by omega⟩ ⟨z,by omega⟩ =
      (1-(z : ℝ))*Real.sqrt (fallingRatio Q z)/Real.sqrt 2 := by
  have hn : 0 < ((2*Q-2).descFactorial z : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : z ≤ 2*Q-2)
  have hf : (0 : ℝ) < z.factorial := by exact_mod_cast z.factorial_pos
  have hq : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  unfold pairCoefficient
  rw [ite_eq_left (by simp [Nat.add_comm] : 1+z=z+1)]
  simp only [Nat.descFactorial_one, Nat.factorial_one, Nat.cast_one, mul_one]
  congr 2
  congr 1
  unfold fallingRatio
  field_simp

lemma pairCoefficient_zero_succ {Q a : ℕ} (hQ : 2 ≤ Q) (hz : a+1 ≤ Q) :
    pairCoefficient Q a 0 ⟨a+1,by omega⟩ =
      -Real.sqrt (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ)/
        ((2*Q-2).descFactorial a : ℝ))/Real.sqrt 2 := by
  have hn : 0 < ((2*Q-2).descFactorial a : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : a ≤ 2*Q-2)
  have hf : (0 : ℝ) < a.factorial := by exact_mod_cast a.factorial_pos
  have hq : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have ha : (0 : ℝ) < (a : ℝ)+1 := by positivity
  have hdesc : Q.descFactorial (a+1) = Q*(Q-1).descFactorial a := by
    have h := Nat.succ_descFactorial_succ (Q-1) a
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Q)] using h
  simp only [pairCoefficient, Fin.val_zero, Nat.zero_add, ite_true,
    Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_sub, Nat.descFactorial_zero,
    Nat.factorial_zero, hdesc, Nat.factorial_succ, Nat.cast_mul, one_mul, mul_one]
  congr 1
  rw [neg_mul, neg_inj]
  rw [show Real.sqrt (((a : ℝ)+1)*((Q-1).descFactorial a : ℝ)/
      ((2*Q-2).descFactorial a : ℝ)) =
      ((a : ℝ)+1)*Real.sqrt (((Q : ℝ)*((Q-1).descFactorial a : ℝ)*(a.factorial : ℝ))/
        ((Q : ℝ)*((2*Q-2).descFactorial a : ℝ)*(((a : ℝ)+1)*(a.factorial : ℝ)))) by
    rw [← Real.sqrt_sq ha.le, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    rw [Real.sqrt_sq ha.le]
    field_simp]

lemma pairCoefficient_zero_formula {Q : ℕ} (hQ : 2 ≤ Q) (i j : Fin (Q+1)) :
    pairCoefficient Q 0 i j =
      if i=⟨1,by omega⟩ ∧ j=0 then 1/Real.sqrt 2
      else if i=0 ∧ j=⟨1,by omega⟩ then -1/Real.sqrt 2 else 0 := by
  have h0 : fallingRatio Q 0 = 1 := by simp [fallingRatio]
  by_cases hi1 : i=⟨1,by omega⟩ ∧ j=0
  · rcases hi1 with ⟨rfl,rfl⟩
    rw [ite_eq_left ⟨rfl,rfl⟩]
    simpa only [Fin.mk_zero, h0, Nat.cast_zero, sub_zero, Real.sqrt_one, mul_one] using
      pairCoefficient_one hQ (Nat.zero_le Q)
  · rw [ite_eq_right hi1]
    by_cases hi0 : i=0 ∧ j=⟨1,by omega⟩
    · rcases hi0 with ⟨rfl,rfl⟩
      rw [ite_eq_left ⟨rfl,rfl⟩]
      simpa only [Nat.cast_zero, zero_add, Nat.descFactorial_zero, Nat.cast_one,
        mul_one, div_one, Real.sqrt_one] using
        pairCoefficient_zero_succ hQ (by omega : 0+1 ≤ Q)
    · rw [ite_eq_right hi0, pairCoefficient, ite_eq_right]
      intro h
      rcases (show i.val=1 ∧ j.val=0 ∨ i.val=0 ∧ j.val=1 by omega) with hh | hh
      · exact hi1 ⟨Fin.ext hh.1,Fin.ext hh.2⟩
      · exact hi0 ⟨Fin.ext hh.1,Fin.ext hh.2⟩

end LaughlinGap.Spin

end

end OAI
