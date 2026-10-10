import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

abbrev projectiveLine (F : Type u) [CommRing F] : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule Bool F)

def constantsInDegreeZero (F : Type u) [CommRing F] :
    F →+* (MvPolynomial.homogeneousSubmodule Bool F 0) where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
  map_one' := Subtype.ext MvPolynomial.C_1
  map_mul' a b := Subtype.ext (MvPolynomial.C_mul (a := a) (a' := b))
  map_zero' := Subtype.ext MvPolynomial.C_0
  map_add' a b := Subtype.ext (MvPolynomial.C_add (a := a) (a' := b))

theorem constantsInDegreeZero_bijective (F : Type u) [CommRing F] :
    Function.Bijective (constantsInDegreeZero F) := by
  constructor
  · intro a b h
    exact MvPolynomial.C_injective _ _ (congrArg Subtype.val h)
  · intro p
    have h : p.val.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr p.property
    refine ⟨p.val.coeff 0, ?_⟩
    apply Subtype.ext
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm

def degreeZeroEquiv (F : Type u) [CommRing F] :
    F ≃+* (MvPolynomial.homogeneousSubmodule Bool F 0) :=
  RingEquiv.ofBijective (constantsInDegreeZero F) (constantsInDegreeZero_bijective F)

instance constantsInDegreeZero_isIso (F : Type u) [CommRing F] :
    IsIso (CommRingCat.ofHom (constantsInDegreeZero F)) :=
  (degreeZeroEquiv F).toCommRingCatIso.isIso_hom

def structureMap (F : Type u) [CommRing F] :
    projectiveLine F ⟶ Spec (CommRingCat.of F) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule Bool F) ≫
    Spec.map (CommRingCat.ofHom (constantsInDegreeZero F))

instance structureMap_isProper (F : Type u) [CommRing F] :
    IsProper (structureMap F) := by
  let A := MvPolynomial Bool F
  let 𝒜 := MvPolynomial.homogeneousSubmodule Bool F
  let : Algebra F (𝒜 0) := SetLike.GradeZero.instAlgebra 𝒜
  let : IsScalarTower F (𝒜 0) A := ⟨fun a b c => by
    change (a • (b : A)) * c = a • ((b : A) * c)
    exact smul_mul_assoc a (b : A) c⟩
  let : Algebra.FiniteType (𝒜 0) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType F (𝒜 0) A
  have hp : IsProper (Proj.toSpecZero 𝒜) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom (constantsInDegreeZero F))) := inferInstance
  unfold structureMap
  exact IsProper.stableUnderComposition.comp_mem _ _ hp inferInstance

end PiExponent.ProjectiveLine

end

end OAI
