import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateConstants
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRingNaturality
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_restrict_apply (i : σ) (a : Finset (ChartVariables i))
    (x : Γ(X,SectionOpens.isoOpen (s i))) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op x) =
      algebraMap _ _ (coordinateSectionRingEquiv M k s hc f hf i x) := by
  have h := coordinateFiniteRingEquiv_restrict M k s hc f hf i a
    (coordinateSectionRingEquiv M k s hc f hf i x)
  simpa only [RingEquiv.symm_apply_apply] using h

lemma coordinateFiniteRingEquiv_coordinate (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (sectionFrame (s i))
            (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))))) =
      algebraMap _ _ (chartToPoly (R := K) i (chartCoordinate i j)) := by
  rw [coordinateFiniteRingEquiv_restrict_apply, coordinateSectionRingEquiv_coordinate]

lemma coordinateFiniteRingEquiv_constant (i : σ) (a : Finset (ChartVariables i)) (r : K) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤ ⊤ from le_top)).op (k r)) =
      algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r) := by
  have h := coordinateFiniteRingEquiv_restrict_apply M s k hc f hf i a
    (X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r))
  rw [coordinateSectionRingEquiv_constant] at h
  convert h using 1
  change _ = coordinateFiniteRingEquiv M s k hc f hf i a
    ((X.presheaf.map _ ≫ X.presheaf.map _) (k r))
  rw [← Functor.map_comp]
  rfl

lemma coordinateFiniteRingEquiv_symm_constant (i : σ) (a : Finset (ChartVariables i)) (r : K) :
    (coordinateFiniteRingEquiv M s k hc f hf i a).symm
      (algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r)) =
    X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤ ⊤ from le_top)).op (k r) := by
  apply (coordinateFiniteRingEquiv M s k hc f hf i a).injective
  rw [RingEquiv.apply_symm_apply, coordinateFiniteRingEquiv_constant]

lemma coordinateFiniteRingEquiv_symm_X (i : σ) (a : Finset (ChartVariables i))
    (j : ChartVariables i) :
    (coordinateFiniteRingEquiv M s k hc f hf i a).symm
      (algebraMap _ _ (MvPolynomial.X (R := K) j)) =
      X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (sectionFrame (s i))
            (restrictSection (SectionOpens.isoOpen (s i)).ι (s j.val)))) := by
  apply (coordinateFiniteRingEquiv M s k hc f hf i a).injective
  rw [RingEquiv.apply_symm_apply, coordinateFiniteRingEquiv_coordinate,
    chartToPoly_coordinate, dite_eq_right j.property]

def coordinateFiniteTransition (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) :
    Localization.Away (chartProduct (R := K) i a) →+*
      Localization.Away (chartProduct (R := K) j b) :=
  (coordinateFiniteRingEquiv M s k hc f hf j b).toRingHom.comp
    ((X.presheaf.map (homOfLE h).op).hom.comp
      (coordinateFiniteRingEquiv M s k hc f hf i a).symm.toRingHom)

lemma coordinateFiniteTransition_constant (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) (r : K) :
    coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r)) =
      algebraMap _ _ (MvPolynomial.C (σ := ChartVariables j) r) := by
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op
      ((coordinateFiniteRingEquiv M s k hc f hf i a).symm _)) = _
  rw [coordinateFiniteRingEquiv_symm_constant]
  change coordinateFiniteRingEquiv M s k hc f hf j b
    ((X.presheaf.map _ ≫ X.presheaf.map _) (k r)) = _
  rw [← Functor.map_comp]
  exact coordinateFiniteRingEquiv_constant M s k hc f hf j b r

lemma coordinateFiniteTransition_same_pivot (i : σ) (a b : Finset (ChartVariables i))
    (h : coordinateFiniteOpen M s i b ≤ coordinateFiniteOpen M s i a)
    (p : MvPolynomial (ChartVariables i) K) :
    coordinateFiniteTransition M s k hc f hf i i a b h (algebraMap _ _ p) =
      algebraMap _ _ p := by
  have he : (coordinateFiniteRingEquiv M s k hc f hf i a).symm (algebraMap _ _ p) =
      X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((coordinateSectionRingEquiv M k s hc f hf i).symm p) := by
    apply (coordinateFiniteRingEquiv M s k hc f hf i a).injective
    rw [RingEquiv.apply_symm_apply, coordinateFiniteRingEquiv_restrict]
  change coordinateFiniteRingEquiv M s k hc f hf i b
    (X.presheaf.map (homOfLE h).op
      ((coordinateFiniteRingEquiv M s k hc f hf i a).symm _)) = _
  rw [he]
  change coordinateFiniteRingEquiv M s k hc f hf i b
    ((X.presheaf.map _ ≫ X.presheaf.map _) _) = _
  rw [← Functor.map_comp]
  exact coordinateFiniteRingEquiv_restrict M k s hc f hf i b p

end
end PiExponentSeshadri.Projective

end OAI
