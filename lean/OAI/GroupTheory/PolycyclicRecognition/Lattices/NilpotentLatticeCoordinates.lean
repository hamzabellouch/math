import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianRealSpace
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelWords

namespace OAI

/-! # Ordered polynomial coordinates for a nilpotent lattice

This record retains the integer parameter alongside the real Lie model.
It is the induction data, not an additional realization hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition
open Module

structure NilpotentLatticeCoordinates (H : Type) [Group H] where
  carrier : Type
  [realNormed : RealNormedLieAlgebra carrier]
  [finiteDimensional : FiniteDimensional ℝ carrier]
  [lieNilpotent : LieRing.IsNilpotent carrier]
  [coordinates : PolynomialExponentialCoordinates carrier]
  [solvable : Group.IsSolvable carrier]
  dimension : ℕ
  basis : Basis (Fin dimension) ℝ carrier
  parameter : carrier ≃ carrier
  polynomial : IsPolynomialInBasis basis basis parameter
  polynomial_symm : IsPolynomialInBasis basis basis parameter.symm
  lattice : Subgroup carrier
  uniform : IsUniformLattice lattice
  equiv : H ≃* lattice
  generators : Fin dimension → H
  word_surjective : Function.Surjective (orderedWord generators)
  integer_parameter : ∀ z : Fin dimension → ℤ,
    parameter (basis.equivFun.symm (fun i => (z i : ℝ))) =
      (equiv (orderedWord generators z) : carrier)

attribute [instance] NilpotentLatticeCoordinates.realNormed
  NilpotentLatticeCoordinates.finiteDimensional NilpotentLatticeCoordinates.lieNilpotent
  NilpotentLatticeCoordinates.coordinates NilpotentLatticeCoordinates.solvable

namespace NilpotentLatticeCoordinates
variable {H K : Type} [Group H] [Group K]

def of_equiv (C : NilpotentLatticeCoordinates H) (e : H ≃* K) :
    NilpotentLatticeCoordinates K where
  carrier := C.carrier
  dimension := C.dimension
  basis := C.basis
  parameter := C.parameter
  polynomial := C.polynomial
  polynomial_symm := C.polynomial_symm
  lattice := C.lattice
  uniform := C.uniform
  equiv := e.symm.trans C.equiv
  generators := fun i => e (C.generators i)
  word_surjective := by
    intro x
    obtain ⟨z, hz⟩ := C.word_surjective (e.symm x)
    refine ⟨z, ?_⟩
    exact (orderedWord_map e.toMonoidHom C.generators z).trans
      ((congrArg e hz).trans (e.apply_symm_apply x))
  integer_parameter := by
    intro z
    have hw : orderedWord (fun i => e (C.generators i)) z =
        e (orderedWord C.generators z) := orderedWord_map e.toMonoidHom C.generators z
    rw [C.integer_parameter, hw]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

def of_subsingleton [Subsingleton H] : NilpotentLatticeCoordinates H := by
  let L := AbelianRealSpace 0
  let : Subsingleton L := inferInstanceAs (Subsingleton (Fin 0 → ℝ))
  let : Unique H := uniqueOfSubsingleton 1
  let : Unique (abelianRealLattice 0) := uniqueOfSubsingleton 1
  let e : H ≃* abelianRealLattice 0 := MulEquiv.ofUnique
  refine {
    carrier := L
    dimension := 0
    basis := Pi.basisFun ℝ (Fin 0)
    parameter := Equiv.refl L
    polynomial := IsPolynomialInBasis.linear (LinearMap.id)
    polynomial_symm := IsPolynomialInBasis.linear (LinearMap.id)
    lattice := abelianRealLattice 0
    uniform := abelianRealLattice_uniform 0
    equiv := e
    generators := Fin.elim0
    word_surjective := ?_
    integer_parameter := ?_ }
  · intro x
    exact ⟨Fin.elim0, Subsingleton.elim _ _⟩
  · intro z
    exact Subsingleton.elim _ _

end NilpotentLatticeCoordinates
end PolycyclicRecognition

end

end OAI
