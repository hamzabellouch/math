import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.FiniteEuler

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

instance Surface.isProper_structureMap (surface : Surface) : IsProper surface.structureMap := by
  have constants_bijective : Function.Bijective
      (constantsInDegreeZero surface.embeddingDimension) := by
    constructor
    · intro left right equality
      have polynomial_equality : MvPolynomial.C left =
          (MvPolynomial.C right : MvPolynomial (Fin (surface.embeddingDimension + 1)) ℂ) :=
        congrArg Subtype.val equality
      exact MvPolynomial.C_injective _ _ polynomial_equality
    · intro polynomial
      have degree_zero : polynomial.val.totalDegree = 0 :=
        (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr polynomial.property
      refine ⟨polynomial.val.coeff 0, ?_⟩
      apply Subtype.ext
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp degree_zero).symm
  let constantsIso := (RingEquiv.ofBijective
    (constantsInDegreeZero surface.embeddingDimension) constants_bijective).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (constantsInDegreeZero surface.embeddingDimension)) :=
    constantsIso.isIso_hom
  let polynomialRing := MvPolynomial (Fin (surface.embeddingDimension + 1)) ℂ
  let grading := MvPolynomial.homogeneousSubmodule (Fin (surface.embeddingDimension + 1)) ℂ
  let : Algebra ℂ (grading 0) := SetLike.GradeZero.instAlgebra grading
  let : IsScalarTower ℂ (grading 0) polynomialRing := ⟨fun scalar homogeneous polynomial => by
    change (scalar • (homogeneous : polynomialRing)) * polynomial =
      scalar • ((homogeneous : polynomialRing) * polynomial)
    exact smul_mul_assoc scalar (homogeneous : polynomialRing) polynomial⟩
  let : Algebra.FiniteType (grading 0) polynomialRing :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grading 0) polynomialRing
  have projective_proper : IsProper (Proj.toSpecZero grading) :=
    Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat grading
  let : IsIso (Spec.map
      (CommRingCat.ofHom (constantsInDegreeZero surface.embeddingDimension))) := by
    infer_instance
  have : IsProper (projectiveSpaceToSpec surface.embeddingDimension) := by
    unfold projectiveSpaceToSpec
    exact IsProper.stableUnderComposition.comp_mem _ _ projective_proper inferInstance
  rw [← surface.overComplex]
  infer_instance

variable {X : Scheme.{0}} [IsIntegral X]

theorem proper_baseScalars_surjective (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] : Function.Surjective (baseScalars p) := by
  have hi : (baseScalars p).IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral (baseScalars p) hi).2

theorem proper_cohomologyDimension_zero_structure
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] :
    cohomologyDimension p (structureSheaf X) 0 = 1 := by
  rw [cohomologyDimension_zero]
  let := Module.compHom Γ(structureSheaf X,⊤) (baseScalars p)
  let f : ℂ →ₗ[ℂ] Γ(structureSheaf X,⊤) :=
    { toFun := baseScalars p
      map_add' := (baseScalars p).map_add
      map_smul' := by intro a b; exact (baseScalars p).map_mul a b }
  have hsur : Function.Surjective f := proper_baseScalars_surjective p
  have hinj : Function.Injective f := (baseScalars p).injective
  let e := LinearEquiv.ofBijective f ⟨hinj,hsur⟩
  exact e.finrank_eq.symm.trans (Module.finrank_self ℂ)

theorem proper_structure_cohomology_zero_finite
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] :
    letI := Module.compHom (cohomology (structureSheaf X) 0) (baseScalars p)
    Module.Finite ℂ (cohomology (structureSheaf X) 0) := by
  let := Module.compHom (cohomology (structureSheaf X) 0) (baseScalars p)
  let := Module.compHom Γ(structureSheaf X,⊤) (baseScalars p)
  let f : ℂ →ₗ[ℂ] Γ(structureSheaf X,⊤) :=
    { toFun := baseScalars p
      map_add' := (baseScalars p).map_add
      map_smul' := by intro a b; exact (baseScalars p).map_mul a b }
  let : Module.Finite ℂ Γ(structureSheaf X,⊤) :=
    Module.Finite.of_surjective f (proper_baseScalars_surjective p)
  exact Module.Finite.of_surjective
    (cohomologyZeroSections p (structureSheaf X)).symm.toLinearMap
    (cohomologyZeroSections p (structureSheaf X)).symm.surjective

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
