import OAI.Analysis.Laughlin.FourBody.RetainedSum
import OAI.Analysis.Laughlin.FourBody.Support

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

theorem fourBody_retained_reconstruction (Q : ℕ) (hQ : 25 ≤ Q)
    (A : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ)
    (hz : ∀ s : FourCoupledIndex Q, 23 < fourCoupledDeficit s →
      A *ᵥ (fun i => (fourCoupledBasis Q i s : ℂ)) = 0) :
    A = ∑ d : Fin 23, ∑ r : OddPairLabel (d.val+1),
      A * retainedFourInclusion Q (d.val+1) (by omega) r *
        (retainedFourInclusion Q (d.val+1) (by omega) r)ᴴ := by
  classical
  have hc : A = (A * (fourCoupledBasis Q).map Complex.ofReal) *
      ((fourCoupledBasis Q).map Complex.ofReal)ᴴ := by
    rw [Matrix.mul_assoc,fourCoupledBasis_complex_complete,Matrix.mul_one]
  ext i j
  have he := congrFun (congrFun hc i) j
  simp only [Matrix.mul_apply,Matrix.map_apply,Matrix.conjTranspose_apply] at he
  rw [he]
  rw [sum_fourCoupled_retained Q hQ
    (fun s => (∑ k, A i k*(fourCoupledBasis Q k s : ℂ))*star (fourCoupledBasis Q j s : ℂ))
    (by intro s hs; have h := congrFun (hz s hs) i; change (∑ k, A i k*_) = 0 at h; rw [h,zero_mul])]
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,retainedFourIndex_column]

theorem physicalFourBodyHaar_high_column (Q : ℕ) (s : FourCoupledIndex Q)
    (hs : 23 < fourCoupledDeficit s) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) *ᵥ
        (fun i => (fourCoupledBasis Q i s : ℂ)) = 0 := by
  let r := oddPairDeficit s.1
  let D := r+s.2.1.val
  have he := physicalFourBodyHaar_high_copy Q r D (oddPairDeficit_le s.1)
    (oddPairDeficit_odd s.1) (by dsimp [D,r]; omega)
    (by have := s.2.1.isLt; dsimp [D,r]; omega)
    (by have := s.2.1.isLt; dsimp [D,r]; omega) hs
  let n : Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1) :=
    ⟨s.2.2.val,by simpa only [D,Nat.add_sub_cancel_left] using s.2.2.isLt⟩
  funext i
  exact congrFun (congrFun he i) n

end Laughlin.Spin

end OAI
