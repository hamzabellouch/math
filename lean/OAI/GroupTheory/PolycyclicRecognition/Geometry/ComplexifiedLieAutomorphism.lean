import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemisimpleLieLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexifiedCartan

namespace OAI

/-! # Complexification of a real semisimple Lie automorphism -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

variable (L : Type) [LieRing L] [LieAlgebra ℝ L]

@[instance_reducible] def complexificationNormedLie [FiniteDimensional ℝ L] :
    ComplexNormedLieAlgebra (ℂ ⊗[ℝ] L) := by
  let b := Module.finBasis ℂ (ℂ ⊗[ℝ] L)
  let : NormedAddCommGroup (ℂ ⊗[ℝ] L) :=
    NormedAddCommGroup.induced _ _ b.equivFun b.equivFun.injective
  let : NormedSpace ℂ (ℂ ⊗[ℝ] L) := NormedSpace.induced ℂ _ _ b.equivFun
  exact { (inferInstance : NormedAddCommGroup (ℂ ⊗[ℝ] L)),
    (inferInstance : LieRing (ℂ ⊗[ℝ] L)), (inferInstance : NormedSpace ℂ (ℂ ⊗[ℝ] L)),
    (inferInstance : LieAlgebra ℂ (ℂ ⊗[ℝ] L)) with }

def complexifiedLieEquiv (S : L ≃ₗ⁅ℝ⁆ L) : (ℂ ⊗[ℝ] L) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] L) :=
  { S.toLinearEquiv.baseChange ℝ ℂ L L with
    map_lie' := by
      intro x y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) S.toLieHom).map_lie x y }

@[simp] theorem complexifiedLieEquiv_tmul (S : L ≃ₗ⁅ℝ⁆ L) (z : ℂ) (x : L) :
    complexifiedLieEquiv L S (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] S x := rfl

def complexificationConjSemilinear : (ℂ ⊗[ℝ] L) →ₗ⋆[ℂ] (ℂ ⊗[ℝ] L) where
  toFun := complexificationConjugation L
  map_add' := map_add (complexificationConjugation L)
  map_smul' := complexificationConjugation_smul L

theorem complexifiedLieEquiv_conj (S : L ≃ₗ⁅ℝ⁆ L) (x : ℂ ⊗[ℝ] L) :
    complexificationConjSemilinear L (complexifiedLieEquiv L S x) =
      complexifiedLieEquiv L S (complexificationConjSemilinear L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem complexifiedEnd_semisimple [FiniteDimensional ℝ L]
    (S : Module.End ℝ L) (hS : S.IsSemisimple) :
    Module.End.IsSemisimple (S.baseChange ℂ) := by
  let f := Module.End.baseChangeHom ℝ ℂ L
  have hp : Squarefree ((minpoly ℝ S).map (algebraMap ℝ ℂ)) :=
    (PerfectField.separable_iff_squarefree.mpr hS.minpoly_squarefree).map.squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp
  have he := Polynomial.map_aeval_eq_aeval_map
    (φ := algebraMap ℝ ℂ) (ψ := f.toRingHom)
    (by apply RingHom.ext; intro r; exact (f.commutes r).symm)
    (minpoly ℝ S) S
  rw [minpoly.aeval, map_zero] at he
  exact he.symm

theorem complexifiedLieEquiv_semisimple [FiniteDimensional ℝ L]
    (S : L ≃ₗ⁅ℝ⁆ L) (hS : Module.End.IsSemisimple S.toLinearMap) :
    Module.End.IsSemisimple (complexifiedLieEquiv L S).toLinearMap :=
  complexifiedEnd_semisimple L S.toLinearMap hS

end PolycyclicRecognition

end

end OAI
