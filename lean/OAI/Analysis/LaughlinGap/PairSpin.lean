import Mathlib
import OAI.Analysis.LaughlinGap.Basic
import OAI.Analysis.LaughlinGap.TensorSpin

namespace OAI

/-! Pair Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

theorem pairCoefficient_binomial {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-1)
    (i j : Fin (Q+1)) :
    pairCoefficient Q p i j = if i.val+j.val=p+1 then
      ((i.val : ℝ)-j.val)*Real.sqrt (Q.choose i.val : ℝ)*Real.sqrt (Q.choose j.val : ℝ) /
        Real.sqrt (2*Q*((2*Q-2).choose p : ℝ)) else 0 := by
  have hch : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show p ≤ 2*Q-2 by omega)).ne'
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  have hrad :
      (((Q.descFactorial i.val : ℝ)*(Q.descFactorial j.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*
          (i.val.factorial : ℝ)*(j.val.factorial : ℝ))) =
      ((Q.choose i.val : ℝ)*Q.choose j.val) / ((Q : ℝ)*((2*Q-2).choose p : ℝ)) := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp
  unfold pairCoefficient
  split_ifs
  · rw [hrad, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity :
        0 ≤ (Q.choose i.val : ℝ)),
      show (2 : ℝ)*Q*((2*Q-2).choose p : ℝ) =
        2*(Q*((2*Q-2).choose p : ℝ)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  · rfl

lemma sqrt_choose_lowering {Q k : ℕ} (hk : k < Q) :
    Real.sqrt (((k : ℝ)+1)*((Q : ℝ)-k))*Real.sqrt (Q.choose k : ℝ) =
      ((k : ℝ)+1)*Real.sqrt (Q.choose (k+1) : ℝ) := by
  have hq : (k : ℝ) ≤ Q := by exact_mod_cast hk.le
  have hc : (Q.choose (k+1) : ℝ)*((k : ℝ)+1) =
      (Q.choose k : ℝ)*((Q : ℝ)-k) := by
    have H := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq Q k)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] using H
  rw [← Real.sqrt_mul (by positivity : 0 ≤ ((k : ℝ)+1)*((Q : ℝ)-k))]
  rw [show (((k : ℝ)+1)*((Q : ℝ)-k))*(Q.choose k : ℝ) =
      (((k : ℝ)+1)^2)*(Q.choose (k+1) : ℝ) by nlinarith [hc]]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

noncomputable def binomialPairTensor (Q p : ℕ) : (Fin (Q+1) × Fin (Q+1)) → ℝ :=
  fun ij => if ij.1.val + ij.2.val = p+1 then
    ((ij.1.val : ℝ)-ij.2.val)*Real.sqrt (Q.choose ij.1.val : ℝ)*
      Real.sqrt (Q.choose ij.2.val : ℝ) else 0

lemma binomialPairTensor_swap (Q p : ℕ) (i j : Fin (Q+1)) :
    binomialPairTensor Q p (j,i) = -binomialPairTensor Q p (i,j) := by
  unfold binomialPairTensor
  by_cases h : i.val+j.val=p+1
  · simp only [h, Nat.add_comm j.val i.val, ite_true]
    ring
  · simp [h, Nat.add_comm j.val i.val]

lemma binomialPairTensor_lower_first (Q p : ℕ) (i j : Fin (Q+1)) :
    lowering Q (fun a => binomialPairTensor Q p (a,j)) i =
      if i.val+j.val=p+2 then
        (i.val : ℝ)*((i.val : ℝ)-1-j.val)*Real.sqrt (Q.choose i.val : ℝ)*
          Real.sqrt (Q.choose j.val : ℝ) else 0 := by
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    rw [lowering_succ]
    simp only [binomialPairTensor, Fin.val_castSucc, Fin.val_succ]
    by_cases h : i.val+j.val=p+1
    · rw [ite_eq_left h, ite_eq_left (by omega : i.val+1+j.val=p+2)]
      simp only [Nat.cast_add, Nat.cast_one, ladderStep]
      have hc := sqrt_choose_lowering i.isLt
      calc
        _ = (((i.val : ℝ)-j.val)*Real.sqrt (Q.choose j.val : ℝ)) *
            (Real.sqrt (((i.val : ℝ)+1)*((Q : ℝ)-i.val))*Real.sqrt (Q.choose i.val : ℝ)) := by ring
        _ = _ := by rw [hc]; ring
    · rw [ite_eq_right h, ite_eq_right (by omega : ¬i.val+1+j.val=p+2), mul_zero]

theorem binomialPairTensor_lower (Q p : ℕ) :
    (tensorSpin Q Q).lower (binomialPairTensor Q p) =
      ((p : ℝ)+1) • binomialPairTensor Q (p+1) := by
  funext ⟨i,j⟩
  rw [tensorSpin_lower, binomialPairTensor_lower_first]
  have hswap : (fun a => binomialPairTensor Q p (i,a)) =
      -(fun a => binomialPairTensor Q p (a,i)) := by
    funext a
    exact binomialPairTensor_swap Q p a i
  rw [hswap, map_neg]
  simp only [Pi.neg_apply]
  rw [binomialPairTensor_lower_first]
  simp only [binomialPairTensor, Pi.smul_apply, smul_eq_mul]
  by_cases h : i.val+j.val=p+2
  · simp only [ite_eq_left h, ite_eq_left (by omega : j.val+i.val=p+2)]
    have hc : (i.val : ℝ)+j.val=(p : ℝ)+2 := by exact_mod_cast h
    rw [show (p : ℝ)+1=(i.val : ℝ)+j.val-1 by linarith]
    ring
  · simp only [ite_eq_right h, ite_eq_right (by omega : ¬j.val+i.val=p+2), neg_zero, zero_add, mul_zero]

noncomputable def physicalPairTensor (Q p : ℕ) : (Fin (Q+1) × Fin (Q+1)) → ℝ :=
  fun ij => pairCoefficient Q p ij.1 ij.2

lemma physicalPairTensor_binomial {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-1) :
    physicalPairTensor Q p =
      (1/Real.sqrt (2*Q*((2*Q-2).choose p : ℝ))) • binomialPairTensor Q p := by
  funext ⟨i,j⟩
  simp only [physicalPairTensor, pairCoefficient_binomial hQ hp, binomialPairTensor,
    Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

lemma pairNormalization_step {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-2) :
    (1/Real.sqrt (2*Q*((2*Q-2).choose p : ℝ)))*((p : ℝ)+1) =
      Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p))*
        (1/Real.sqrt (2*Q*((2*Q-2).choose (p+1) : ℝ))) := by
  have hc := sqrt_choose_lowering hp
  have hs0 : Real.sqrt (((2*Q-2).choose p : ℝ)) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    exact_mod_cast Nat.choose_pos hp.le
  have hs1 : Real.sqrt (((2*Q-2).choose (p+1) : ℝ)) ≠ 0 := by
    apply (Real.sqrt_pos.mpr _).ne'
    exact_mod_cast Nat.choose_pos hp
  simp only [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2*Q)]
  field_simp
  nlinarith [congrArg (fun a => a*Real.sqrt (2*(Q : ℝ))) hc]

theorem physicalPairTensor_lower {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p < 2*Q-2) :
    (tensorSpin Q Q).lower (physicalPairTensor Q p) =
      Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p)) • physicalPairTensor Q (p+1) := by
  rw [physicalPairTensor_binomial hQ (by omega), map_smul, binomialPairTensor_lower,
    physicalPairTensor_binomial hQ (by omega), smul_smul, smul_smul,
    pairNormalization_step hQ hp]

lemma highestWeight_first_one {Q : ℕ} (hQ : 0 < Q) :
    highestWeight Q Q 1 1 = 1 := by
  have hQr : (Q : ℝ) ≠ 0 := by positivity
  simp only [highestWeight, Nat.choose_self, Nat.cast_one, Finset.prod_range_one,
    one_mul, highestFactor, Nat.cast_zero, sub_zero]
  rw [show (Q : ℝ)-1+0+1 = Q by ring, div_self hQr]

lemma highestNormalization_first {Q : ℕ} (hQ : 0 < Q) :
    highestNormalization Q Q 1 = 2 := by
  norm_num [highestNormalization, Finset.sum_range_succ, highestWeight_first_one hQ]

lemma sqrt_Q_over_sqrt_twoQ {Q : ℕ} (hQ : 0 < Q) :
    Real.sqrt (Q : ℝ)/Real.sqrt (2*Q : ℝ) = 1/Real.sqrt 2 := by
  have hQr : Real.sqrt (Q : ℝ) ≠ 0 := by positivity
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

theorem physicalPairTensor_zero {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalPairTensor Q 0 = highestTensor Q Q 1 := by
  have hQ0 : 0 < Q := by omega
  funext ⟨i,j⟩
  simp only [physicalPairTensor, pairCoefficient_binomial hQ (by omega : 0 < 2*Q-1),
    highestTensor]
  by_cases h : i.val+j.val=1
  · rw [ite_eq_left h, ite_eq_left h]
    rcases (show i.val=0 ∧ j.val=1 ∨ i.val=1 ∧ j.val=0 by omega) with hij | hij
    · simp only [hij.1, hij.2, Nat.cast_zero, Nat.cast_one, zero_sub,
        Nat.choose_zero_right, Nat.choose_one_right, mul_one, highestCoefficient,
        highestWeight_zero, highestNormalization_first hQ0]
      simp only [Nat.sub_zero, pow_one, Real.sqrt_one, one_mul, neg_mul, neg_div]
      exact congrArg Neg.neg (sqrt_Q_over_sqrt_twoQ hQ0)
    · simp only [hij.1, hij.2, Nat.cast_zero, Nat.cast_one, sub_zero,
        Nat.choose_zero_right, Nat.choose_one_right, mul_one, one_mul, highestCoefficient,
        highestWeight_first_one hQ0, highestNormalization_first hQ0,
        Nat.sub_self, pow_zero, Real.sqrt_one]
      exact sqrt_Q_over_sqrt_twoQ hQ0
  · simp only [ite_eq_right h]

theorem physicalPairTensor_eq_coupled {Q p : ℕ} (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    physicalPairTensor Q p = coupledTensor Q Q 1 p := by
  have hz : 1 ≤ min Q Q := by omega
  have hd : Q+Q-2*1=2*Q-2 := by omega
  rw [coupledTensor_eq_normalized hz (by omega), hd]
  induction p with
  | zero => rw [LadderSystem.normalized_zero, physicalPairTensor_zero hQ]
  | succ p ih =>
    have hl : p < 2*Q-2 := by omega
    have ha : Real.sqrt (((p : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-p)) ≠ 0 := by
      apply (Real.sqrt_pos.mpr _).ne'
      have hpr : (p : ℝ) < (2*Q-2 : ℕ) := by exact_mod_cast hl
      exact mul_pos (by positivity) (by linarith)
    rw [LadderSystem.normalized_succ _ _ hl, ← ih (by omega), physicalPairTensor_lower hQ hl,
      smul_smul, one_div_mul_cancel ha, one_smul]

end LaughlinGap.Spin

end

end OAI
