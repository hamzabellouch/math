import OAI.Analysis.Laughlin.FourBody.TargetBound
import OAI.Analysis.Laughlin.Pair.CoupledOne

namespace OAI

namespace Laughlin.Fock
open Spin
open scoped BigOperators Matrix Kronecker

theorem pairCoupledOne_contract (Q : ℕ) (hQ : 1 ≤ Q)
    (n : Fin (genericCoupledWeight Q Q 1+1)) (x : Space Q) :
    (∑ i : WedgePairIndex Q, (pairCoupledInclusion Q 1 hQ i n : ℂ) •
      annihilate i.val.2 (annihilate i.val.1 x)) = sourcePairEnd Q n.val x := by
  have hf (i j : Fin (Q+1)) : annihilate i (annihilate j x) =
      -annihilate j (annihilate i x) := by
    have h := LinearMap.congr_fun (annihilate_anticommute i j) x
    exact eq_neg_of_add_eq_zero_left h
  have he := antisymmetric_exterior_sum Q
    (fun i => annihilate i.2 (annihilate i.1 x)) hf
    (fun i => ((pairCoefficient Q n.val i.1 i.2 / Real.sqrt 2 : ℝ) : ℂ))
  have hn : n.val ≤ 2*Q-2 := by have := n.isLt; unfold genericCoupledWeight at this; omega
  have hc (i : WedgePairIndex Q) :
      ((pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 : ℝ) : ℂ) -
        ((pairCoefficient Q n.val i.val.2 i.val.1 / Real.sqrt 2 : ℝ) : ℂ) =
      (pairCoupledInclusion Q 1 hQ i n : ℂ) := by
    rw [pairCoefficient_swap Q n.val i.val.1 i.val.2]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    have hreal : pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 -
        -pairCoefficient Q n.val i.val.1 i.val.2 / Real.sqrt 2 =
      Real.sqrt 2*pairCoefficient Q n.val i.val.1 i.val.2 := by
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    rw [← Complex.ofReal_sub,hreal]
    simp only [pairCoupledInclusion,pairCoupledWedge,tensorToWedgePair,pairCoupledTensor_one Q n.val hQ hn]
  have he' := he.trans (Finset.sum_congr rfl (fun i hi =>
    congrArg (fun c : ℂ => c • annihilate i.val.2 (annihilate i.val.1 x)) (hc i)))
  calc
    _ = ∑ i : SpinIndex Q Q, ((pairCoefficient Q n.val i.1 i.2 / Real.sqrt 2 : ℝ) : ℂ) •
        annihilate i.2 (annihilate i.1 x) := he'.symm
    _ = _ := by
      simp only [sourcePairEnd,pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,
        Module.End.mul_apply,Fintype.sum_prod_type]

theorem fourPairEmbedding_contract (Q : ℕ) (hQ : 1 ≤ Q)
    (j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1)) (x : Space Q) :
    (∑ i : FourWedgeIndex Q, star (fourPairEmbedding Q 1 hQ i j) • sourceFourFamilyEnd Q i x) =
      sourcePairEnd Q j.2.val (sourcePairEnd Q j.1.val x) := by
  simp only [fourPairEmbedding,Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,
    Matrix.map_apply,apply_ite,star_zero,Complex.star_def,Complex.conj_ofReal,
    ite_mul,one_mul,zero_mul,ite_smul,zero_smul,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  exact pairCoupledOne_contract Q hQ j.2 (sourcePairEnd Q j.1.val x)

theorem contractionForm_factor_one {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (Q : ℕ) (L : I → Module.End ℂ (Space Q)) (W : Matrix I J ℂ) (x : Space Q) :
    contractionForm Q L (W*Wᴴ) x =
      (∑ j, (occupationNormSq Q (∑ i, star (W i j) • L i x) : ℂ)) := by
  have h := occupation_matrix_quadratic_factor Q W (1 : Matrix J J ℂ) (fun i => L i x)
  rw [Matrix.mul_one] at h
  change (∑ a, ∑ b, (W*Wᴴ) a b * occupationInner Q (L a x) (L b x)) = _
  rw [← h]
  simp [Matrix.one_apply,occupationInner_self]

theorem fourPairTargetMatrix_Fock (Q : ℕ) (hQ : 1 ≤ Q) (x : Space Q) :
    (contractionForm Q (sourceFourFamilyEnd Q) (fourPairTargetMatrix Q hQ) x).re =
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) := by
  rw [fourPairTargetMatrix,contractionForm_factor_one]
  simp only [Complex.re_sum,Complex.ofReal_re]
  have he : (∑ j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1),
      occupationNormSq Q (∑ i, star (fourPairEmbedding Q 1 hQ i j) • sourceFourFamilyEnd Q i x)) =
      ∑ j : SpinIndex (2*Q-2) (genericCoupledWeight Q Q 1),
        occupationNormSq Q (sourcePairEnd Q j.2.val (sourcePairEnd Q j.1.val x)) :=
    Finset.sum_congr rfl (fun j hj => congrArg (occupationNormSq Q) (fourPairEmbedding_contract Q hQ j x))
  rw [he,Fintype.sum_prod_type]
  have hw : genericCoupledWeight Q Q 1=2*Q-2 := by unfold genericCoupledWeight; omega
  apply Finset.sum_congr rfl
  intro p hp
  exact Fintype.sum_equiv (finCongr (congrArg (fun m => m+1) hw)) _ _ (fun q => rfl)

theorem sourceA4Form_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤
      (∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))) +
      (10946*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  have ht := retainedFourTarget_le_full Q hQ x
  rw [fourPairTargetMatrix_Fock] at ht
  have hb := sourceA4Form_retained_bound Q hQ x
  linarith

end Laughlin.Fock

end OAI
