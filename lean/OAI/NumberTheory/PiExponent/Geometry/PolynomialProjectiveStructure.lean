import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable (R σ : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialGradeZeroEquiv : R ≃+* homogeneousSubmodule σ R 0 :=
  RingEquiv.ofBijective (algebraMap R (homogeneousSubmodule σ R 0)) (by
    constructor
    · intro a b h
      apply MvPolynomial.C_injective
      exact congrArg (fun x : homogeneousSubmodule σ R 0 => (x : MvPolynomial σ R)) h
    · intro p
      refine ⟨p.1.coeff 0, ?_⟩
      apply Subtype.ext
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr p.2)).symm)

def polynomialProjectiveProjection : Proj (homogeneousSubmodule σ R) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (homogeneousSubmodule σ R) ≫
    Spec.map (CommRingCat.ofHom (polynomialGradeZeroEquiv R σ).toRingHom)

instance : IsScalarTower R (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := homogeneousSubmodule σ R 0)
    (A := MvPolynomial σ R) (fun _ => rfl)

instance [Finite σ] : Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R
    (homogeneousSubmodule σ R 0) (MvPolynomial σ R)

instance polynomialProjectiveProjection_proper [Finite σ] :
    IsProper (polynomialProjectiveProjection R σ) := by
  have : IsProper (Proj.toSpecZero (homogeneousSubmodule σ R)) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom (polynomialGradeZeroEquiv R σ).toRingHom)) := by
    change IsIso (Spec.map (polynomialGradeZeroEquiv R σ).toCommRingCatIso.hom)
    infer_instance
  exact MorphismProperty.comp_mem (@IsProper) _ _ inferInstance inferInstance

end PiExponent

end

end OAI
