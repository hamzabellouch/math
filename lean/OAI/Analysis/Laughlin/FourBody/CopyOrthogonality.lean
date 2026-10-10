import OAI.Analysis.Laughlin.FourBody.Copies
import OAI.Analysis.Laughlin.Spin.Basis2

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def fourBodyInclusion (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q)
      (Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1)) ℝ :=
  tensorPairInclusion (2*Q-2) Q r hr *
    ((-1 : ℝ)^(D-r) • genericCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB)

theorem fourBodyInclusion_column (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (n : Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1))
    (i : Fin (2*Q-2+1) × WedgePairIndex Q) :
    fourBodyInclusion Q r D hr hA hB i n = fourBodyCopy Q r D hr hA hB n.val i := rfl

theorem pairCoupledInclusion_cross (Q r s : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hor : Odd r) (hos : Odd s) (hne : r ≠ s) :
    (pairCoupledInclusion Q r hr)ᵀ * pairCoupledInclusion Q s hs = 0 := by
  ext n m
  exact pairCoupledWedge_orthogonal Q r s n.val m.val hr hs hor hos (Or.inl hne)

theorem tensorPairInclusion_cross (A Q r s : ℕ) (hr : r ≤ Q) (hs : s ≤ Q)
    (hor : Odd r) (hos : Odd s) (hne : r ≠ s) :
    (tensorPairInclusion A Q r hr)ᵀ * tensorPairInclusion A Q s hs = 0 := by
  unfold tensorPairInclusion
  have ht : ((1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ pairCoupledInclusion Q r hr)ᵀ =
      (1 : Matrix (Fin (A+1)) (Fin (A+1)) ℝ) ⊗ₖ (pairCoupledInclusion Q r hr)ᵀ := by
    ext i j
    simp [Matrix.kroneckerMap,Matrix.transpose_apply,Matrix.one_apply,eq_comm]
  rw [ht,← Matrix.mul_kronecker_mul,pairCoupledInclusion_cross Q r s hr hs hor hos hne]
  simp

theorem fourBodyInclusion_isometry (Q r D : ℕ) (hr : r ≤ Q) (hor : Odd r)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    (fourBodyInclusion Q r D hr hA hB)ᵀ * fourBodyInclusion Q r D hr hA hB = 1 := by
  have hs : (-1 : ℝ)^(D-r) * (-1 : ℝ)^(D-r) = 1 := by rw [← mul_pow]; norm_num
  unfold fourBodyInclusion
  rw [Matrix.transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc
    (tensorPairInclusion (2*Q-2) Q r hr)ᵀ,
    tensorPairInclusion_isometry _ Q r hr hor,Matrix.one_mul]
  simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    genericCoupledInclusion_isometry,hs,one_smul]

theorem fourBodyCopy_orthogonal_pair (Q r s D E n m : ℕ)
    (hr : r ≤ Q) (hs : s ≤ Q) (hor : Odd r) (hos : Odd s) (hne : r ≠ s)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hC : E-s ≤ 2*Q-2) (hD : E-s ≤ genericCoupledWeight Q Q s) :
    (∑ i, fourBodyCopy Q r D hr hA hB n i * fourBodyCopy Q s E hs hC hD m i) = 0 := by
  have hp {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
      (A : Matrix I J ℝ) (B : Matrix I K ℝ) (v : J → ℝ) (w : K → ℝ) :
      (∑ i, (A *ᵥ v) i * (B *ᵥ w) i) = ∑ j, v j * ((Aᵀ*B) *ᵥ w) j := by
    change (A *ᵥ v) ⬝ᵥ (B *ᵥ w) = v ⬝ᵥ ((Aᵀ*B) *ᵥ w)
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_transpose_mulVec]
    exact dotProduct_comm _ _
  rw [fourBodyCopy,fourBodyCopy,hp,tensorPairInclusion_cross _ Q r s hr hs hor hos hne]
  simp

theorem fourBodyCopy_orthogonal_outer (Q r D E n m : ℕ)
    (hr : r ≤ Q) (hor : Odd r) (hrD : r ≤ D) (hrE : r ≤ E)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (hC : E-r ≤ 2*Q-2) (hD : E-r ≤ genericCoupledWeight Q Q r)
    (hne : D ≠ E ∨ n ≠ m) :
    (∑ i, fourBodyCopy Q r D hr hA hB n i * fourBodyCopy Q r E hr hC hD m i) = 0 := by
  have hp {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
      (A : Matrix I J ℝ) (h : Aᵀ*A=1) (v w : J → ℝ) :
      (∑ i, (A *ᵥ v) i * (A *ᵥ w) i) = ∑ j, v j*w j := by
    change (A *ᵥ v) ⬝ᵥ (A *ᵥ w) = v ⬝ᵥ w
    rw [← Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,h,Matrix.one_mulVec]
    exact dotProduct_comm _ _
  rw [fourBodyCopy,fourBodyCopy,hp _ (tensorPairInclusion_isometry _ Q r hr hor)]
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    _ = ((-1 : ℝ)^(D-r) * (-1 : ℝ)^(E-r)) *
      (∑ i, genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB n i *
        genericUnitDescendant (2*Q-2) (genericCoupledWeight Q Q r) (E-r) hC hD m i) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    _ = 0 := by
      rw [genericUnitDescendant_orthogonal _ _ _ _ _ _ hA hB hC hD (by
        rcases hne with h | h
        · left; omega
        · exact Or.inr h),mul_zero]

end Laughlin.Spin

end OAI
