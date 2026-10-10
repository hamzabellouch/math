import OAI.NumberTheory.PiExponent.Approximation.WeightedCompactification
import OAI.NumberTheory.PiExponent.Polynomials.SurjectiveGradedMap

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

universe u
variable {R ι σ : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev projectiveMonomialMap (a : σ → ι →₀ ℕ) :
    Proj (imageGrade (R := R) a) ⟶ Proj (homogeneousSubmodule σ R) :=
  Proj.map (gradedImageMap a) (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))

@[simp]
theorem projectiveMonomialMap_preimage (a : σ → ι →₀ ℕ) (s : σ) :
    projectiveMonomialMap (R := R) a ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X s) =
      Proj.basicOpen (imageGrade a) (imageCoordinate a s) := rfl


theorem projectiveMonomialMap_restrict (a : σ → ι →₀ ℕ) (s : σ) :
    projectiveMonomialMap (R := R) a ∣_ Proj.basicOpen (homogeneousSubmodule σ R) (X s) =
      (Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
        ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map (gradedImageMap (R := R) a) (X s))) ≫
          (Proj.basicOpenIsoSpec _ _ (isHomogeneous_X R s) (by decide)).inv := by
  let e := Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
    ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)
  apply (cancel_epi e.inv).1
  apply (cancel_mono (Proj.basicOpen (homogeneousSubmodule σ R) (X s)).ι).1
  have h := Proj.awayι_comp_map (gradedImageMap (R := R) a)
    (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))
    (by decide : 0 < (1 : ℕ)) (X s) (isHomogeneous_X R s)
  simp only [Category.assoc, e, Iso.inv_hom_id_assoc]
  erw [Category.assoc, morphismRestrict_ι]
  simpa only [Proj.awayι, Category.assoc, projectiveMonomialMap,
    Proj.map_preimage_basicOpen] using h

instance projectiveMonomialMap_isClosedImmersion (a : σ → ι →₀ ℕ) :
    IsClosedImmersion (projectiveMonomialMap (R := R) a) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun s : σ => Proj.basicOpen (homogeneousSubmodule σ R) (X s)) (standardChart_cover)
  intro s
  rw [projectiveMonomialMap_restrict]
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Away.map (gradedImageMap (R := R) a) (X s)))) :=
    IsClosedImmersion.spec_of_surjective _
      (homogeneousAway_map_surjective (gradedImageMap a) (gradedImageMap_surjective a)
        (isHomogeneous_X R s))
  let eB := Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
    ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)
  let eA := Proj.basicOpenIsoSpec (homogeneousSubmodule σ R) (X s)
    (isHomogeneous_X R s) (by decide)
  change IsClosedImmersion (eB.hom ≫ _ ≫ eA.inv)
  have : IsClosedImmersion eB.hom := inferInstance
  have : IsClosedImmersion eA.inv := inferInstance
  exact IsClosedImmersion.comp _ _

end PiExponent.WeightedCompactification

end

end OAI
