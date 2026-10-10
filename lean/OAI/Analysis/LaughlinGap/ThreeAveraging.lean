import Mathlib
import OAI.Analysis.LaughlinGap.FourAveraging
import OAI.Analysis.LaughlinGap.ThreeBounds

namespace OAI

/-! Three Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def lowCoupledInclusion {n m T : ℕ} (hT : T ≤ min n m)
    (z : Fin (T+1)) : CoupledIndex n m :=
  ⟨⟨z.val, by omega⟩, ⟨T-z.val, by dsimp; have := z.isLt; omega⟩⟩

lemma coupledTensor_low_expansion {n m T : ℕ} (hT : T ≤ min n m)
    (a : Fin (n+1) × Fin (m+1)) (ha : a.1.val+a.2.val=T) :
    (∑ z : Fin (T+1), coupledTensor n m z.val (T-z.val) a •
      coupledTensor n m z.val (T-z.val)) = Pi.single a 1 := by
  classical
  have hex := coupledTensor_expansion n m (Pi.single a 1)
  simp only [dotProduct_single_one] at hex
  rw [← hex]
  apply Finset.sum_bij_ne_zero (fun z _ _ => lowCoupledInclusion hT z)
  · simp
  · intro z hz hz0 w hw hw0 he
    exact Fin.ext (congrArg (fun i : CoupledIndex n m => i.1.val) he)
  · intro b hb hb0
    have hw : b.1.val+b.2.val=T := by
      by_contra hn
      exact hb0 (by simp [coupledTensor, show a.1.val+a.2.val ≠ b.1.val+b.2.val by omega])
    let z : Fin (T+1) := ⟨b.1.val,by omega⟩
    have hz : lowCoupledInclusion hT z = b := by
      rcases b with ⟨r,l⟩
      have hr : (lowCoupledInclusion hT z).1 = r := Fin.ext rfl
      apply Sigma.ext hr
      apply (Fin.heq_ext_iff (by rfl)).mpr
      dsimp [lowCoupledInclusion,z]
      dsimp at hw
      omega
    refine ⟨z,Finset.mem_univ _,?_,hz⟩
    change coupledTensor n m (lowCoupledInclusion hT z).1.val
      (lowCoupledInclusion hT z).2.val a • coupledTensor n m
      (lowCoupledInclusion hT z).1.val (lowCoupledInclusion hT z).2.val ≠ 0
    rwa [hz]
  · intros
    rfl

lemma coupledEmbedding_single {n m z : ℕ} (hz : z ≤ min n m)
    (l : Fin (n+m-2*z+1)) :
    (coupledEmbedding hz).toLinearMap (Pi.single l 1) = coupledTensor n m z l.val := by
  rw [coupledEmbedding_apply]
  simp [Pi.single_apply, ite_smul]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma Covariant.coupled_average {n m z w T U : ℕ}
    (hT : T ≤ min n m) (hU : U ≤ min n m) (hz : z ≤ T) (hw : w ≤ U)
    {L : Matrix ι ι ℝ} {B : (Fin (n+1) × Fin (m+1)) → Matrix ι ι ℝ}
    (h : Covariant L (loweringMatrix (tensorSpin n m)) B) :
    average (rotationCommutant L)
      ((combination B (coupledTensor n m z (T-z))).transpose *
        combination B (coupledTensor n m w (U-w))) =
      if z=w ∧ T=U then
        average (rotationCommutant L)
          ((combination B (highestTensor n m z)).transpose *
            combination B (highestTensor n m z)) else 0 := by
  let hz' : z ≤ min n m := hz.trans hT
  let hw' : w ≤ min n m := hw.trans hU
  rw [← coupledEmbedding_single hz' (⟨T-z,by omega⟩ : Fin (n+m-2*z+1)),
    ← coupledEmbedding_single hw' (⟨U-w,by omega⟩ : Fin (n+m-2*w+1))]
  by_cases hzw : z=w
  · subst w
    rw [h.equal_descendant_average]
    simp only [coupledEmbedding_single, Fin.val_zero, coupledTensor_zero, true_and,
      Fin.mk.injEq]
    congr 1
    apply propext
    omega
  · rw [ite_eq_right (by tauto)]
    exact h.distinct_descendant_average (by omega) _ _ _ _

lemma Covariant.rawTensor_cross_average {n m T : ℕ} (hT : T ≤ min n m)
    {L : Matrix ι ι ℝ} {B : (Fin (n+1) × Fin (m+1)) → Matrix ι ι ℝ}
    (h : Covariant L (loweringMatrix (tensorSpin n m)) B)
    (a b : Fin (n+1) × Fin (m+1))
    (ha : a.1.val+a.2.val=T) (hb : b.1.val+b.2.val=T) :
    average (rotationCommutant L) ((B a).transpose * B b) =
      ∑ z : Fin (T+1),
        (coupledCoefficient n m z.val (T-z.val) a.1.val *
          coupledCoefficient n m z.val (T-z.val) b.1.val) •
        average (rotationCommutant L)
          ((combination B (highestTensor n m z.val)).transpose *
            combination B (highestTensor n m z.val)) := by
  classical
  have hex (c : Fin (n+1) × Fin (m+1)) (hc : c.1.val+c.2.val=T) :=
    congrArg (combination B) (coupledTensor_low_expansion hT c hc)
  have hea := hex a ha
  have heb := hex b hb
  simp only [map_sum, map_smul, combination_single] at hea heb
  rw [← hea, ← heb]
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, Finset.sum_mul, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_sum, map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hh (w : Fin (T+1)) := h.coupled_average hT hT
    (Nat.le_of_lt_succ z.isLt) (Nat.le_of_lt_succ w.isLt)
  simp only [hh, and_true, Fin.val_inj]
  rw [Finset.sum_eq_single z]
  · simp only [ite_true, coupledTensor, show a.1.val+a.2.val=z.val+(T-z.val) by omega,
      show b.1.val+b.2.val=z.val+(T-z.val) by omega]
    rw [mul_comm]
  · intro w hw hwz
    rw [ite_eq_right (Ne.symm hwz), smul_zero]
  · simp

lemma rawTriple_cross_average {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a b : Fin (2*Q-2+1) × Fin (Q+1))
    (ha : a.1.val+a.2.val=T) (hb : b.1.val+b.2.val=T) :
    average (rotationCommutant (fockLowering Q))
      ((physicalTriple Q a).transpose * physicalTriple Q b) =
      ∑ z : Fin (T+1),
        (coupledCoefficient (2*Q-2) Q z.val (T-z.val) a.1.val *
          coupledCoefficient (2*Q-2) Q z.val (T-z.val) b.1.val /
            ((2*Q-2)+Q-2*z.val+1 : ℕ)) •
          threeSpinLift hQ (show z.val ≤ Q by omega) := by
  rw [(physicalTriple_covariant hQ).rawTensor_cross_average (by omega) a b ha hb]
  apply Finset.sum_congr rfl
  intro z hz
  rw [threeSpinLift_average_highest hQ (show z.val ≤ Q by omega), smul_smul]
  congr 1
  ring

end LaughlinGap.RealOccupation

end

end OAI
