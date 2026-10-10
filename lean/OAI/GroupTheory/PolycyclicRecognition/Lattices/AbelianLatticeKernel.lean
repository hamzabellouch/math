import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeInnerAdjoint

namespace OAI

/-! # Commutativity passes to the actual nilpotent lattice completion -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open scoped IsMulCommutative
variable {N : Type} [Group N] [IsMulCommutative N] (C : NilpotentLatticeCoordinates N)

theorem completed_kernel_mul_comm (u v : C.carrier) : u * v = v * u := by
  have hl (n : N) (x : C.carrier) : (C.equiv n : C.carrier) * x * (C.equiv n : C.carrier)⁻¹ = x := by
    rw [← C.automorphism_inner_apply]
    have hn : MulAut.conj n = 1 := by
      apply DFunLike.ext
      intro y
      change n * y * n⁻¹ = y
      rw [mul_comm n y, mul_inv_cancel_right]
    rw [hn, C.automorphism_one]
    rfl
  have hp : IsPolynomialInBasis C.basis C.basis
      (fun x : C.carrier => u * x * u⁻¹) := by
    have he : (fun x : C.carrier => u * x * u⁻¹) = adjointLinearMap (E := C.carrier) u :=
      funext (fun x => (polynomial_adjoint_apply u x).symm)
    rw [he]
    exact IsPolynomialInBasis.linear (adjointLinearMap (E := C.carrier) u).toLinearMap
  have he : (fun x : C.carrier => u * x * u⁻¹) = id :=
    C.ext_polynomial hp (IsPolynomialInBasis.linear (LinearMap.id)) (by
      intro n
      have hn := hl n u
      rw [mul_inv_eq_iff_eq_mul] at hn
      change u * (C.equiv n : C.carrier) * u⁻¹ = C.equiv n
      rw [← hn, mul_inv_cancel_right])
  exact mul_inv_eq_iff_eq_mul.mp (congrFun he v)

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
