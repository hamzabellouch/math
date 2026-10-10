import OAI.Analysis.Laughlin.Pair.CoupledIsometry
import OAI.Analysis.Laughlin.Spin.Support

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def tensorPairInclusion (A Q r : ℕ) (hr : r ≤ Q) :
    Matrix (Fin (A+1) × WedgePairIndex Q) (SpinIndex A (genericCoupledWeight Q Q r)) ℝ :=
  (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ pairCoupledInclusion Q r hr

theorem tensorPairInclusion_isometry (A Q r : ℕ) (hr : r ≤ Q) (ho : Odd r) :
    (tensorPairInclusion A Q r hr)ᵀ * tensorPairInclusion A Q r hr = 1 := by
  unfold tensorPairInclusion
  have ht : ((1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ pairCoupledInclusion Q r hr)ᵀ =
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ (pairCoupledInclusion Q r hr)ᵀ := by
    ext i j
    simp [Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]
  rw [ht,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,pairCoupledInclusion_isometry Q r hr ho,
    Matrix.one_kronecker_one]

theorem isometry_vectorNormSq {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (W : Matrix I J ℝ) (hW : Wᵀ*W=1) (f : J → ℝ) :
    vectorNormSq (W *ᵥ f) = vectorNormSq f := by
  unfold vectorNormSq
  simp only [pow_two]
  have hp (v : J → ℝ) (w : I → ℝ) :
      (∑ i, (W *ᵥ v) i*w i) = ∑ i, v i*(Wᵀ *ᵥ w) i := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj; ring
  rw [hp,Matrix.mulVec_mulVec,hW,Matrix.one_mulVec]

noncomputable def fourBodyCopy (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (n : ℕ) :
    Fin ((2*Q-2)+1) × WedgePairIndex Q → ℝ :=
  tensorPairInclusion (2*Q-2) Q r hr *ᵥ
    ((-1 : ℝ)^(D-r) • genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r)
      (D-r) hA hB n)

theorem phased_generic_norm (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n ≤ genericCoupledWeight A B z) :
    vectorNormSq ((-1 : ℝ)^z • genericUnitDescendant A B z hA hB n) = 1 := by
  unfold vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  have h : ((-1 : ℝ)^z)^2 = 1 := by rw [← pow_mul,mul_comm z 2,pow_mul]; norm_num
  rw [h,one_mul]
  exact genericUnitDescendant_norm A B z n hA hB hn

theorem fourBodyCopy_norm (Q r D n : ℕ) (hr : r ≤ Q) (ho : Odd r)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hn : n ≤ genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)) :
    vectorNormSq (fourBodyCopy Q r D hr hA hB n) = 1 := by
  rw [fourBodyCopy,isometry_vectorNormSq _ (tensorPairInclusion_isometry _ Q r hr ho)]
  exact phased_generic_norm _ _ _ _ hA hB hn

theorem fourBodyCopy_coordinate (Q r D n : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q) :
    fourBodyCopy Q r D hr hA hB n (p,i) =
      ∑ b : Fin (genericCoupledWeight Q Q r+1), pairCoupledWedge Q r hr b.val i *
        ((-1 : ℝ)^(D-r) * genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r)
          (D-r) hA hB n (p,b)) := by
  simp only [fourBodyCopy,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,tensorPairInclusion,
    Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,ite_mul,
    one_mul,zero_mul,pairCoupledInclusion,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end Laughlin.Spin

end OAI
