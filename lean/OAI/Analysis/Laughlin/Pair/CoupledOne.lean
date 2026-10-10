import OAI.Analysis.Laughlin.Pair.CoupledParity
import OAI.Analysis.Laughlin.Pair.LadderIntertwining

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem highestUnit_one_zero (Q : ℕ) (hQ : 1 ≤ Q) :
    highestUnit Q Q 1 0 = 1 / Real.sqrt 2 := by
  have hn := highestUnit_norm Q Q 1 hQ hQ
  have hr := highestUnit_reverse Q 1 0 (by omega)
  norm_num at hr
  simp only [show 1+1=2 by omega,Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at hn
  rw [hr] at hn
  have hp : 0 < highestUnit Q Q 1 0 := by
    rw [highestUnit,highestRaw_zero]
    have hqr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    simp only [Nat.choose_one_right]
    exact div_pos (by positivity) (highestNorm_pos Q Q 1 hQ hQ)
  have ht : 0 < (1 : ℝ)/Real.sqrt 2 := by positivity
  have hs : ((1 : ℝ)/Real.sqrt 2)^2 = 1/2 := by
    rw [div_pow,Real.sq_sqrt (by norm_num)]; norm_num
  nlinarith only [hn,hp,ht,hs]

theorem pairCoupledTensor_one_zero (Q : ℕ) (hQ : 1 ≤ Q) (i : SpinIndex Q Q) :
    pairCoupledTensor Q 1 hQ 0 i = pairCoefficient Q 0 i.1 i.2 := by
  rw [pairCoupledTensor,genericUnitDescendant_zero]
  simp only [pow_one,Pi.smul_apply,smul_eq_mul,neg_one_mul]
  by_cases hi : i.1.val+i.2.val=1
  · let p : Fin 2 := ⟨i.1.val,by omega⟩
    have he : i = weightSliceIndex Q Q 1 hQ hQ p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    have hv : genericHighest Q Q 1 hQ hQ i = highestUnit Q Q 1 i.1.val := by
      change extendWeightSlice Q Q 1 hQ hQ _ i = _
      rw [he,extendWeightSlice_at]; rfl
    rw [hv]
    have hqr : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    rcases (show i.1.val=0 ∨ i.1.val=1 by omega) with h0 | h1
    · have hj : i.2.val=1 := by omega
      simp [pairCoefficient,h0,hj,highestUnit_one_zero Q hQ,hqr,div_eq_mul_inv]
    · have hj : i.2.val=0 := by omega
      have hr := highestUnit_reverse Q 1 0 (by omega)
      norm_num at hr
      rw [h1,hr,highestUnit_one_zero Q hQ]
      simp [pairCoefficient,h1,hj,hqr]
  · have hv : genericHighest Q Q 1 hQ hQ i = 0 :=
      extendWeightSlice_off Q Q 1 hQ hQ _ i hi
    simp [hv,pairCoefficient,hi]

theorem pairCoupledTensor_lowering (Q r n : ℕ) (hr : r ≤ Q)
    (hn : n < genericCoupledWeight Q Q r) :
    (totalRaise Q Q)ᵀ *ᵥ pairCoupledTensor Q r hr n =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q r : ℝ)-n)) •
        pairCoupledTensor Q r hr (n+1) := by
  rw [pairCoupledTensor,Matrix.mulVec_smul,genericUnitDescendant_lowering Q Q r n hr hr hn]
  exact smul_comm _ _ _

theorem pairCoupledTensor_one (Q n : ℕ) (hQ : 1 ≤ Q) (hn : n ≤ 2*Q-2)
    (i : SpinIndex Q Q) :
    pairCoupledTensor Q 1 hQ n i = pairCoefficient Q n i.1 i.2 := by
  induction n generalizing i with
  | zero => exact pairCoupledTensor_one_zero Q hQ i
  | succ n ih =>
    have hcw : genericCoupledWeight Q Q 1 = 2*Q-2 := by unfold genericCoupledWeight; omega
    have hlt : n < genericCoupledWeight Q Q 1 := by rw [hcw]; omega
    have hreal : (n : ℝ) < genericCoupledWeight Q Q 1 := by exact_mod_cast hlt
    have hd : Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q 1 : ℝ)-n)) ≠ 0 := by positivity
    have he := congrFun (pairCoupledTensor_lowering Q 1 n hQ hlt) i
    have hf : pairCoupledTensor Q 1 hQ n = fun j => pairCoefficient Q n j.1 j.2 := by
      funext j; exact ih (by omega) j
    rw [hf] at he
    change (∑ j, totalRaise Q Q j i * pairCoefficient Q n j.1 j.2) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight Q Q 1 : ℝ)-n))*
        pairCoupledTensor Q 1 hQ (n+1) i at he
    rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column] at he
    have hc := pairCoefficient_tensor_lowering Q n (by omega) (by omega) i.1 i.2
    have hl : pairTensorLower Q n i.1 i.2 =
        (∑ j, totalRaise Q Q j i * pairCoefficient Q n j.1 j.2) := by
      rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column]
      unfold pairTensorLower; split_ifs <;> ring
    rw [hcw] at he hd
    have hw : ladder (2*Q-2) n = Real.sqrt (((n : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-n)) := by
      unfold ladder
      rw [Nat.cast_sub (by omega : n ≤ 2*Q-2)]
    rw [hw] at hc
    have he' : pairTensorLower Q n i.1 i.2 =
      Real.sqrt (((n : ℝ)+1)*(((2*Q-2 : ℕ) : ℝ)-n))*pairCoupledTensor Q 1 hQ (n+1) i := by
      rw [hl,totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column]
      exact he
    exact (mul_left_cancel₀ hd) (he'.symm.trans hc)

end Laughlin.Spin

end OAI
