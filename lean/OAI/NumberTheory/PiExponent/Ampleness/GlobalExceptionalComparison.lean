import OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction
import OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction
import OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso

namespace OAI

noncomputable section
namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)

abbrev affineCenterIdeal :=
  (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩

@[reassoc (attr := simp)] theorem affineRestrictionIso_hom_reesProjection :
    (affineRestrictionIso I U).hom ≫ ReesGrading.projection (affineCenterIdeal I U) =
      ((projection I) ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom := by
  have h := congrArg (fun f => f ≫ U.1.toScheme.isoSpec.hom)
    (affineRestrictionIso_hom_projection I U)
  simpa only [AffineBlowup.projection, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using h

def restrictedExceptionalLineBundle :=
  (exceptionalLineBundle I).restrict ((projection I) ⁻¹ᵁ U.1).ι

def restrictedExceptionalInclusion :
    (restrictedExceptionalLineBundle I U).sheaf ⟶
      structureSheaf (((projection I) ⁻¹ᵁ U.1).toScheme) :=
  InvertibleLocal.restrictedInclusion (exceptionalLineBundle I)
    (exceptionalInclusion I) ((projection I) ⁻¹ᵁ U.1).ι

def affineExceptionalOnRestriction :=
  InvertibleLocal.restrictLineBundle
    (ReesGrading.exceptionalLineBundle (affineCenterIdeal I U))
    (affineRestrictionIso I U).hom

def affineExceptionalInclusionOnRestriction :
    (affineExceptionalOnRestriction I U).sheaf ⟶
      structureSheaf (((projection I) ⁻¹ᵁ U.1).toScheme) :=
  InvertibleLocal.restrictedInclusion
    (ReesGrading.exceptionalLineBundle (affineCenterIdeal I U))
    (ReesGrading.exceptionalInclusion (affineCenterIdeal I U))
    (affineRestrictionIso I U).hom

theorem restrictedExceptional_presents :
    PresentsPullbackIdeal (IdealPullback.specIdeal (affineCenterIdeal I U))
      (((projection I) ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom)
      (restrictedExceptionalLineBundle I U) (restrictedExceptionalInclusion I U) :=
  presents_post_toSpec _ _
    (presents_morphismRestrict _ _ (exceptional_presents I) U)

theorem affineExceptionalOnRestriction_presents :
    PresentsPullbackIdeal (IdealPullback.specIdeal (affineCenterIdeal I U))
      (((projection I) ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom)
      (affineExceptionalOnRestriction I U) (affineExceptionalInclusionOnRestriction I U) := by
  have h := InvertibleLocal.presents_restrict_general _ _ _ _
    (ReesGrading.exceptional_presents (affineCenterIdeal I U))
    (affineRestrictionIso I U).hom
  rw [affineRestrictionIso_hom_reesProjection] at h
  exact h

def exceptionalAffineIso :
    (restrictedExceptionalLineBundle I U).sheaf ≅
      (affineExceptionalOnRestriction I U).sheaf :=
  PiExponent.PresentedIdealIso.iso _ _ _ _ _ _
    (restrictedExceptional_presents I U) (affineExceptionalOnRestriction_presents I U)

@[reassoc (attr := simp)] theorem exceptionalAffineIso_hom_inclusion :
    (exceptionalAffineIso I U).hom ≫ affineExceptionalInclusionOnRestriction I U =
      restrictedExceptionalInclusion I U :=
  PiExponent.PresentedIdealIso.iso_hom_inclusion _ _ _ _ _ _ _ _

def exceptionalAffinePowerIso (n : ℕ) :
    ((restrictedExceptionalLineBundle I U).pow n).sheaf ≅
      ((affineExceptionalOnRestriction I U).pow n).sheaf :=
  (modulePowFunctor n).mapIso (exceptionalAffineIso I U)

@[reassoc (attr := simp)] theorem exceptionalAffinePowerIso_hom_inclusion (n : ℕ) :
    (exceptionalAffinePowerIso I U n).hom ≫
      modulePowMap (affineExceptionalInclusionOnRestriction I U) n =
        modulePowMap (restrictedExceptionalInclusion I U) n := by
  change modulePowMap (exceptionalAffineIso I U).hom n ≫
    modulePowMap (affineExceptionalInclusionOnRestriction I U) n = _
  rw [← modulePowMap_comp, exceptionalAffineIso_hom_inclusion]

def restrictedExceptionalPowerAffineIso (n : ℕ) :
    ((exceptionalLineBundle I).pow n).sheaf.restrict ((projection I) ⁻¹ᵁ U.1).ι ≅
      ((affineExceptionalOnRestriction I U).pow n).sheaf :=
  modulePowRestrict ((projection I) ⁻¹ᵁ U.1) (exceptionalLineBundle I).sheaf n ≪≫
    exceptionalAffinePowerIso I U n

end PiExponentSeshadri.BlowupGluing

end

end OAI
