import OAI.Analysis.Laughlin.FourBody.RetainedInclusions
import OAI.Analysis.Laughlin.Operators.GenericPhysicalResolution

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def fourPairEmbedding (Q r : ℕ) (hr : r ≤ Q) :
    Matrix (FourWedgeIndex Q) (SpinIndex (2*Q-2) (genericCoupledWeight Q Q r)) ℂ :=
  (1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) ⊗ₖ
    (pairCoupledInclusion Q r hr).map Complex.ofReal

theorem fourPairEmbedding_resolution (Q r : ℕ) (hr : r ≤ Q) :
    fourPairEmbedding Q r hr*(fourPairEmbedding Q r hr)ᴴ =
      ∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
        fourWedgeInclusion Q r (r+z.val) hr (by omega) (by omega) *
          (fourWedgeInclusion Q r (r+z.val) hr (by omega) (by omega))ᴴ := by
  let F : Matrix (FourWedgeIndex Q) (SpinIndex (2*Q-2) (genericCoupledWeight Q Q r)) ℂ :=
    fourPairEmbedding Q r hr
  have hA (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) : z.val ≤ 2*Q-2 :=
    (Nat.le_of_lt_succ z.isLt).trans (Nat.min_le_left _ _)
  have hB (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) : z.val ≤ genericCoupledWeight Q Q r :=
    (Nat.le_of_lt_succ z.isLt).trans (Nat.min_le_right _ _)
  have hp (z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1)) :
      fourWedgeInclusion Q r (r+z.val) hr (by simpa only [Nat.add_sub_cancel_left] using hA z) (by simpa only [Nat.add_sub_cancel_left] using hB z) *
        (fourWedgeInclusion Q r (r+z.val) hr (by simpa only [Nat.add_sub_cancel_left] using hA z) (by simpa only [Nat.add_sub_cancel_left] using hB z))ᴴ =
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z)) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ := by
    rw [fourWedgeInclusion_factor]
    let v : {k : ℕ // k ≤ 2*Q-2 ∧ k ≤ genericCoupledWeight Q Q r} →
        Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ := fun k =>
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) k.val k.property.1 k.property.2) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) k.val k.property.1 k.property.2)ᴴ
    exact congrArg v (show (⟨r+z.val-r,by constructor <;> omega⟩ :
      {k : ℕ // k ≤ 2*Q-2 ∧ k ≤ genericCoupledWeight Q Q r}) = ⟨z.val,by constructor <;> omega⟩
      from Subtype.ext (Nat.add_sub_cancel_left r z.val))
  change F*Fᴴ = _
  calc
    _ = F*(∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
      physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z) *
        (physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ)*Fᴴ := by
      rw [physicalCoupledInclusion_complete,Matrix.mul_one]
    _ = ∑ z : Fin (min (2*Q-2) (genericCoupledWeight Q Q r)+1),
      (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z)) *
        (F*physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) z.val (hA z) (hB z))ᴴ := by
      simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = _ := Finset.sum_congr rfl (fun z hz => (hp z).symm)

noncomputable def fourPairTargetMatrix (Q : ℕ) (hQ : 1 ≤ Q) :
    Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ :=
  fourPairEmbedding Q 1 hQ*(fourPairEmbedding Q 1 hQ)ᴴ

end Laughlin.Spin

end OAI
