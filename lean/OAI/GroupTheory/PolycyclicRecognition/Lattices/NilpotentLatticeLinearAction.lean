import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeAutomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-! # A faithful linear action of the discrete lattice automorphisms

The constructed action is the differential of the actual smooth extension.
It is not a separately assumed representation of the discrete group.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
variable {H : Type} [Group H] (C : PolycyclicRecognition.NilpotentLatticeCoordinates H)

def automorphismLinear : MulAut H →* Module.End ℝ C.carrier where
  toFun a := (C.automorphismLieEquiv a).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change C.automorphismLieEquiv 1 x = x
    rw [C.automorphismLieEquiv_apply, C.automorphism_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    change C.automorphismLieEquiv (a * b) x =
      C.automorphismLieEquiv a (C.automorphismLieEquiv b x)
    simp only [C.automorphismLieEquiv_apply, C.automorphism_mul, MulAut.mul_apply]

@[simp] theorem automorphismLinear_apply (a : MulAut H) (x : C.carrier) :
    C.automorphismLinear a x = C.automorphism a x :=
  C.automorphismLieEquiv_apply a x

theorem automorphismLinear_injective : Function.Injective C.automorphismLinear := by
  intro a b h
  apply C.automorphism_injective
  apply DFunLike.ext
  intro x
  change C.automorphism a x = C.automorphism b x
  have he := congrArg (fun F : Module.End ℝ C.carrier => F x) h
  simpa only [C.automorphismLinear_apply] using he

def automorphismMatrix : MulAut H →*
    Matrix.GeneralLinearGroup (Fin C.dimension) ℝ :=
  (Units.map (LinearMap.toMatrixAlgEquiv C.basis).toMonoidHom).comp
    C.automorphismLinear.toHomUnits

theorem automorphismMatrix_injective : Function.Injective C.automorphismMatrix := by
  intro a b h
  apply C.automorphismLinear_injective
  exact (LinearMap.toMatrixAlgEquiv C.basis).injective (congrArg Units.val h)

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
