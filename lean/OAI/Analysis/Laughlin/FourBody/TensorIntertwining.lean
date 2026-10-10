import OAI.Analysis.Laughlin.FourBody.Copies
import OAI.Analysis.Laughlin.Spin.Disjoint
import OAI.Analysis.Laughlin.Spin.Intertwining

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

abbrev FourTensorIndex (Q : ℕ) := Fin (2*Q-2+1) × SpinIndex Q Q

noncomputable def fourTensorInclusion (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    Matrix (FourTensorIndex Q)
      (Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1)) ℂ :=
  ((1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) ⊗ₖ
    physicalCoupledInclusion Q Q r hr hr) *
    physicalCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB

noncomputable def fourTensorRepresentation (Q : ℕ) :
    SourceSU2 →* Matrix (FourTensorIndex Q) (FourTensorIndex Q) ℂ where
  toFun g := sourceSpinRepresentation (2*Q-2) g ⊗ₖ
    (sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g)
  map_one' := by simp only [map_one,Matrix.one_kronecker_one]
  map_mul' g h := by simp only [map_mul,Matrix.mul_kronecker_mul]

theorem fourTensorRepresentation_continuous (Q : ℕ) (i j : FourTensorIndex Q) :
    Continuous (fun g => fourTensorRepresentation Q g i j) :=
  (sourceSpinRepresentation_continuous (2*Q-2) i.1 j.1).mul
    ((sourceSpinRepresentation_continuous Q i.2.1 j.2.1).mul
      (sourceSpinRepresentation_continuous Q i.2.2 j.2.2))

theorem fourTensorRepresentation_inv (Q : ℕ) (g : SourceSU2) :
    fourTensorRepresentation Q g⁻¹ = (fourTensorRepresentation Q g)ᴴ := by
  change _ ⊗ₖ (_ ⊗ₖ _) = (_ ⊗ₖ (_ ⊗ₖ _))ᴴ
  simp only [Matrix.conjTranspose_kronecker,sourceSpinRepresentation_inv]

theorem fourTensorInclusion_SU2 (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (g : SourceSU2) :
    fourTensorRepresentation Q g * fourTensorInclusion Q r D hr hA hB =
      fourTensorInclusion Q r D hr hA hB *
        sourceSpinRepresentation
          (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)) g := by
  unfold fourTensorInclusion
  change (_ ⊗ₖ _) * ((_ ⊗ₖ _) * _) = _
  rw [← Matrix.mul_assoc,← Matrix.mul_kronecker_mul,Matrix.mul_one,
    physicalCoupledInclusion_SU2]
  have he : sourceSpinRepresentation (2*Q-2) g ⊗ₖ
      (physicalCoupledInclusion Q Q r hr hr * sourceSpinRepresentation (genericCoupledWeight Q Q r) g) =
      ((1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) ⊗ₖ
        physicalCoupledInclusion Q Q r hr hr) *
        (sourceSpinRepresentation (2*Q-2) g ⊗ₖ sourceSpinRepresentation (genericCoupledWeight Q Q r) g) := by
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
  rw [he,Matrix.mul_assoc,physicalCoupledInclusion_SU2,Matrix.mul_assoc]

noncomputable def fourWedgeInclusion (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q)
      (Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1)) ℂ :=
  fun i n => (fourBodyCopy Q r D hr hA hB n.val i : ℂ)

theorem fourTensorInclusion_coordinate (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (i : FourTensorIndex Q)
    (n : Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1)) :
    fourTensorInclusion Q r D hr hA hB i n =
      ∑ b : Fin (genericCoupledWeight Q Q r+1),
        (pairCoupledTensor Q r hr b.val i.2 : ℂ) *
        ((-1 : ℂ)^(D-r) * (genericUnitDescendant (2*Q-2)
          (genericCoupledWeight Q Q r) (D-r) hA hB n.val (i.1,b) : ℂ)) := by
  simp only [fourTensorInclusion,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kroneckerMap,Matrix.of_apply,Matrix.one_apply,
    ite_mul,one_mul,zero_mul,physicalCoupledInclusion,Matrix.smul_apply,
    smul_eq_mul,Matrix.map_apply,genericCoupledInclusion,
    pairCoupledTensor,Pi.smul_apply,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem fourWedgeInclusion_tensor_coordinate (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (i : Fin (2*Q-2+1) × WedgePairIndex Q)
    (n : Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1)) :
    fourWedgeInclusion Q r D hr hA hB i n =
      (Real.sqrt 2 : ℂ) * fourTensorInclusion Q r D hr hA hB (i.1,i.2.val) n := by
  rw [fourWedgeInclusion,fourBodyCopy_coordinate,fourTensorInclusion_coordinate]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one,pairCoupledWedge,tensorToWedgePair,
    Complex.ofReal_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

end Laughlin.Spin

end OAI
