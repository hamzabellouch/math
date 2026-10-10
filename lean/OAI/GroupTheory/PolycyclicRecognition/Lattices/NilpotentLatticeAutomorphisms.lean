import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilpotentLatticeCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeWordExtension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelHom

namespace OAI

/-! # Extending the lattice automorphism group to its nilpotent Lie model

The extension respects composition. This retains arbitrary discrete actions,
without imposing unipotence on their automorphisms.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {H : Type} [Group H]

namespace NilpotentLatticeCoordinates
variable (C : NilpotentLatticeCoordinates H)

theorem ext_polynomial {f g : C.carrier → C.carrier}
    (hf : IsPolynomialInBasis C.basis C.basis f)
    (hg : IsPolynomialInBasis C.basis C.basis g)
    (h : ∀ x : H, f (C.equiv x) = g (C.equiv x)) : f = g := by
  have hp : f ∘ C.parameter = g ∘ C.parameter :=
    (hf.comp C.polynomial).ext_integer_grid (hg.comp C.polynomial) (by
      intro z
      change f (C.parameter (C.basis.equivFun.symm (fun i => (z i : ℝ)))) =
        g (C.parameter (C.basis.equivFun.symm (fun i => (z i : ℝ))))
      rw [C.integer_parameter]
      exact h _)
  funext x
  obtain ⟨y, rfl⟩ := C.parameter.surjective x
  exact congrFun hp y

def automorphism (a : MulAut H) : MulAut C.carrier :=
  latticeWordAut C.basis C.parameter (C.lattice.subtype.comp C.equiv.toMonoidHom)
    C.generators C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a

theorem automorphism_polynomial (a : MulAut H) :
    IsPolynomialInBasis C.basis C.basis (C.automorphism a) :=
  latticeWordMap_polynomial C.basis C.parameter
    (C.lattice.subtype.comp C.equiv.toMonoidHom) C.generators
    C.polynomial_symm a.toMonoidHom

theorem automorphism_smooth (a : MulAut H) :
    ContMDiff (𝓘(ℝ, C.carrier)) (𝓘(ℝ, C.carrier)) ∞ (C.automorphism a) :=
  contMDiff_latticeWordAut C.basis C.parameter
    (C.lattice.subtype.comp C.equiv.toMonoidHom) C.generators
    C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a

@[simp] theorem automorphism_on_lattice (a : MulAut H) (x : H) :
    C.automorphism a (C.equiv x) = (C.equiv (a x) : C.carrier) :=
  latticeWordAut_on_lattice C.basis C.parameter
    (C.lattice.subtype.comp C.equiv.toMonoidHom) C.generators
    C.polynomial C.polynomial_symm C.integer_parameter C.word_surjective a x

@[simp] theorem automorphism_one : C.automorphism 1 = 1 := by
  apply DFunLike.ext
  intro x
  have h : (C.automorphism 1 : C.carrier → C.carrier) = id :=
    C.ext_polynomial (C.automorphism_polynomial 1)
      (IsPolynomialInBasis.linear (LinearMap.id)) (by intro y; simp)
  exact congrFun h x

@[simp] theorem automorphism_mul (a b : MulAut H) :
    C.automorphism (a * b) = C.automorphism a * C.automorphism b := by
  apply DFunLike.ext
  intro x
  have h : (C.automorphism (a * b) : C.carrier → C.carrier) =
      (C.automorphism a : C.carrier → C.carrier) ∘ C.automorphism b :=
    C.ext_polynomial (C.automorphism_polynomial (a * b))
      ((C.automorphism_polynomial a).comp (C.automorphism_polynomial b)) (by
        intro y
        change C.automorphism (a * b) (C.equiv y) =
          C.automorphism a (C.automorphism b (C.equiv y))
        rw [C.automorphism_on_lattice, C.automorphism_on_lattice, C.automorphism_on_lattice]
        rfl)
  exact congrFun h x

def automorphismHom : MulAut H →* MulAut C.carrier where
  toFun := C.automorphism
  map_one' := C.automorphism_one
  map_mul' := C.automorphism_mul

theorem automorphism_injective : Function.Injective C.automorphismHom := by
  intro a b h
  apply DFunLike.ext
  intro x
  apply C.equiv.injective
  apply Subtype.ext
  have he := congrArg (fun f : MulAut C.carrier => f (C.equiv x)) h
  simpa only [automorphismHom, MonoidHom.coe_mk, OneHom.coe_mk,
    C.automorphism_on_lattice] using he

def automorphismLieEquiv (a : MulAut H) : C.carrier ≃ₗ⁅ℝ⁆ C.carrier :=
  polynomialModelLieEquiv (C.automorphism a) (C.automorphism_smooth a)

@[simp] theorem automorphismLieEquiv_apply (a : MulAut H) (x : C.carrier) :
    C.automorphismLieEquiv a x = C.automorphism a x :=
  polynomialModelLieEquiv_apply _ _ _

end NilpotentLatticeCoordinates
end PolycyclicRecognition

end

end OAI
