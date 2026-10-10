import Mathlib
import OAI.Analysis.LaughlinGap.FourAveraging
import OAI.Analysis.LaughlinGap.RealSpinSquare

namespace OAI

/-! Four. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma tensorProjection_positive {n m z : ℕ} (hz : z ≤ min n m) :
    (tensorProjection hz).PosSemidef := by
  rw [tensorProjection_eq]
  apply Matrix.posSemidef_sum
  intro l hl
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    (coupledTensor n m z l.val)

lemma sum_tensorProjection (n m : ℕ) :
    (∑ z : Fin (min n m+1), tensorProjection (Nat.le_of_lt_succ z.isLt)) = 1 := by
  classical
  ext a b
  have h := congrFun (coupledTensor_expansion n m (Pi.single b 1)) a
  simpa only [tensorProjection_eq, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Fintype.sum_sigma, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    dotProduct_single_one, Pi.single_apply, Matrix.one_apply, eq_comm, mul_comm] using h.symm

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma Covariant.average_highest {n m z : ℕ} (hz : z ≤ min n m)
    {L : Matrix ι ι ℝ} {B : (Fin (n+1) × Fin (m+1)) → Matrix ι ι ℝ}
    (h : Covariant L (loweringMatrix (tensorSpin n m)) B) :
    average (rotationCommutant L)
      ((combination B (highestTensor n m z)).transpose * combination B (highestTensor n m z)) =
    (1/(n+m-2*z+1 : ℕ) : ℝ) • lift B (tensorProjection hz) := by
  have he : (coupledEmbedding hz).toLinearMap (Pi.single (0 : Fin (n+m-2*z+1)) 1) =
      highestTensor n m z := by
    rw [coupledEmbedding_apply]
    simp [Pi.single_apply, ite_smul]
  rw [← lift_rankOne, h.average_lift, ← he, equal_copy_average]
  simp only [ite_true, map_smul]
  simp only [tensorProjection, LadderMap.comp, LadderMap.transpose,
    LinearMap.toMatrix'_comp, toMatrix_transposeMap, LadderMap.matrix]

noncomputable def physicalPairPair (Q : ℕ) :
    (Fin (2*Q-2+1) × Fin (2*Q-2+1)) → FockMatrix (Q+1) :=
  productFamily (fun p => physicalPair Q p.val) (fun p => physicalPair Q p.val)

lemma physicalPairPair_covariant {Q : ℕ} (hQ : 2 ≤ Q) :
    Covariant (fockLowering Q) (loweringMatrix (tensorSpin (2*Q-2) (2*Q-2)))
      (physicalPairPair Q) := (physicalPair_covariant hQ).product (physicalPair_covariant hQ)

lemma fourAnnihilator_first {Q D T : ℕ} (hQ : 2 ≤ Q) :
    fourAnnihilator Q D T 1 =
      combination (physicalPairPair Q) (coupledTensor (2*Q-2) (2*Q-2) (D-1) (T-D)) := by
  classical
  unfold fourAnnihilator
  unfold nestedTensor
  rw [show Q+Q-2*1=2*Q-2 by omega]
  simp only [combination, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type,
    physicalFour, productFamily, smul_smul, Finset.sum_mul, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← physicalPairTensor_eq_coupled hQ (Nat.le_of_lt_succ r.isLt)]
  simp only [physicalPairPair, productFamily, physicalPair, combination,
    LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type, Matrix.smul_mul,
    Finset.sum_mul, Finset.smul_sum, smul_smul, Matrix.mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  ring

lemma lift_physicalPairPair_one {Q : ℕ} (hQ : 2 ≤ Q) :
    lift (physicalPairPair Q) 1 = fourTarget Q := by
  rw [lift_identity]
  simp only [physicalPairPair, productFamily, Fintype.sum_prod_type, fourTarget]
  let e : Fin (2*Q-2+1) ≃ Fin (2*Q-1) := finCongr (by omega)
  have he := e.sum_comp (fun p : Fin (2*Q-1) => ∑ q : Fin (2*Q-1),
    (physicalPair Q q.val * physicalPair Q p.val).transpose *
      (physicalPair Q q.val * physicalPair Q p.val))
  rw [← he]
  apply Finset.sum_congr rfl
  intro p hp
  exact e.sum_comp (fun q : Fin (2*Q-1) =>
    (physicalPair Q q.val * physicalPair Q p.val).transpose *
      (physicalPair Q q.val * physicalPair Q p.val))

theorem fourTarget_retained {Q K : ℕ} (hQ : 2 ≤ Q) (hK : K ≤ Q) :
    (∑ d : Fin K, ((4*Q-1-2*(d.val+1) : ℕ) : ℝ) •
      average (rotationCommutant (fockLowering Q))
        ((fourAnnihilator Q (d.val+1) (d.val+1) 1).transpose *
          fourAnnihilator Q (d.val+1) (d.val+1) 1)) ≤ fourTarget Q := by
  classical
  have hz (d : Fin K) : d.val ≤ min (2*Q-2) (2*Q-2) := by omega
  have he (d : Fin K) :
    ((4*Q-1-2*(d.val+1) : ℕ) : ℝ) • average (rotationCommutant (fockLowering Q))
      ((fourAnnihilator Q (d.val+1) (d.val+1) 1).transpose *
        fourAnnihilator Q (d.val+1) (d.val+1) 1) =
      lift (physicalPairPair Q) (tensorProjection (hz d)) := by
    rw [fourAnnihilator_first hQ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, coupledTensor_zero]
    rw [(physicalPairPair_covariant hQ).average_highest (hz d), smul_smul]
    have hn : 4*Q-1-2*(d.val+1) = (2*Q-2)+(2*Q-2)-2*d.val+1 := by omega
    rw [hn, mul_one_div_cancel (by positivity), one_smul]
  simp only [he]
  rw [← lift_physicalPairPair_one hQ, ← sum_tensorProjection (2*Q-2) (2*Q-2), map_sum]
  let e : Fin K ↪ Fin (min (2*Q-2) (2*Q-2)+1) :=
    ⟨fun d => ⟨d.val,Nat.lt_succ_of_le (hz d)⟩,
      fun a b he => Fin.ext (congrArg (fun z : Fin (min (2*Q-2) (2*Q-2)+1) => z.val) he)⟩
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (s := Finset.univ.map e) (t := Finset.univ)
    (f := fun z : Fin (min (2*Q-2) (2*Q-2)+1) =>
      lift (physicalPairPair Q) (tensorProjection (Nat.le_of_lt_succ z.isLt)))
    (Finset.subset_univ _) (fun z _ _ => (lift_positive _ (tensorProjection_positive _)).nonneg)
  simpa only [Finset.sum_map, e, Function.Embedding.coeFn_mk] using hh

end LaughlinGap.RealOccupation

end

end OAI
