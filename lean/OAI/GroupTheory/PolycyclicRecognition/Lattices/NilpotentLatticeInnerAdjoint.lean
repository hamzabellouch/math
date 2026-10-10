import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeInnerAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialInnerAdjoint

namespace OAI

/-! # The exact inner action on a constructed nilpotent lattice model -/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open scoped Manifold
variable {H : Type} [Group H] (C : NilpotentLatticeCoordinates H)

theorem automorphism_inner_apply (t : H) (v : C.carrier) :
    C.automorphism (MulAut.conj t) v = (C.equiv t : C.carrier) * v * (C.equiv t : C.carrier)⁻¹ := by
  let u : C.carrier := C.equiv t
  let B := polynomialModelLieHom (MulAut.conj u).toMonoidHom
    ((contMDiff_conjugation u).of_le (by simp))
  have hB : (B : C.carrier → C.carrier) = fun v => u * v * u⁻¹ := by
    funext v
    exact polynomialModelLieHom_apply _ _ v
  have hpoly : IsPolynomialInBasis C.basis C.basis (fun v => u * v * u⁻¹) := by
    rw [← hB]
    exact IsPolynomialInBasis.linear B.toLinearMap
  have he : (C.automorphism (MulAut.conj t) : C.carrier → C.carrier) =
      fun v => u * v * u⁻¹ := C.ext_polynomial (C.automorphism_polynomial _) hpoly (by
    intro y
    rw [C.automorphism_on_lattice]
    simp only [MulAut.conj_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl)
  exact congrFun he v

theorem automorphismLinear_inner_exp (t : H) :
    LinearMap.toContinuousLinearMap (C.automorphismLinear (MulAut.conj t)) =
      NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ C.carrier (C.equiv t))) := by
  apply ContinuousLinearMap.ext
  intro v
  change C.automorphismLinear (MulAut.conj t) v = _
  rw [C.automorphismLinear_apply, C.automorphism_inner_apply t v]
  exact polynomial_inner_eq_exp_ad _ _

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
