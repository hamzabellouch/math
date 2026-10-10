import Mathlib

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeTriviality
open CategoryTheory AlgebraicGeometry Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R]
abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 2) R
def line : Scheme := Proj (grading R)
def constants : R →+* grading R 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
def toBase : line R ⟶ Spec (.of R) :=
  AlgebraicGeometry.Proj.toSpecZero (grading R) ≫ Spec.map (CommRingCat.ofHom (constants R))

def fiberProjection (p : PrimeSpectrum R) :
    pullback (toBase R) (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) ⟶ line R :=
  pullback.fst _ _

def awayProjection (r : R) :
    pullback (toBase R) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) ⟶ line R :=
  pullback.fst _ _

instance constants_isIso : IsIso (CommRingCat.ofHom (constants R)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro r s h
    exact MvPolynomial.C_injective (Fin 2) R (congrArg Subtype.val h)
  · intro p
    refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr p.property)).symm
instance line_toBase_universallyClosed : UniversallyClosed (toBase R) := by
  have : Algebra.FiniteType (grading R 0) (MvPolynomial (Fin 2) R) := by
    apply RingHom.finiteType_algebraMap.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := constants R)
    change (algebraMap R (MvPolynomial (Fin 2) R)).FiniteType
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hproj : UniversallyClosed (AlgebraicGeometry.Proj.toSpecZero (grading R)) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom (constants R))) := inferInstance
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (constants R))) := inferInstance
  have hspec : UniversallyClosed (Spec.map (CommRingCat.ofHom (constants R))) := inferInstance
  unfold toBase
  exact @AlgebraicGeometry.universallyClosedTypeComp _ _ _ _ _ hproj hspec
end CampanaPeternellSix.RelativeTriviality

end

end OAI
