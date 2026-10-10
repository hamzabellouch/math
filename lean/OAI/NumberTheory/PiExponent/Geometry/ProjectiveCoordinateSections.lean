import OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames
import OAI.NumberTheory.PiExponent.Approximation.TensorPowerRestriction
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartOverlaps
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveChartSections
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateValues

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] MvPolynomial.gradedAlgebra

def schemeIsoGammaEquiv {Y : Scheme} {A : CommRingCat} (g : Y ≅ Spec A) :
    Γ(Y,⊤) ≃+* A :=
  (Scheme.Γ.mapIso g.symm.op ≪≫ Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

@[simp] lemma schemeIsoGammaEquiv_symm_apply {Y : Scheme} {A : CommRingCat}
    (g : Y ≅ Spec A) (a : A) :
    (schemeIsoGammaEquiv g).symm a = ((Scheme.ΓSpecIso A).inv ≫ g.hom.appTop).hom a := rfl

private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (k : K →+* Γ(X,⊤))
variable (s : σ → (O X ⟶ M)) (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
include hf

lemma sectionOpen_eq_coordinate_preimage (i : σ) :
    SectionOpens.isoOpen (s i) = f.hom ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
  rw [← hf]
  exact (sectionsMorphism_preimage k s hc i).symm

def coordinateSectionChartIso (i : σ) :
    (SectionOpens.isoOpen (s i)).toScheme ≅ Spec (CommRingCat.of (PolyChart (R := K) i)) :=
  X.isoOfEq (sectionOpen_eq_coordinate_preimage M k s hc f hf i) ≪≫
    f.hom.preimageIso (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) ≪≫
      Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)

lemma coordinateSectionChartIso_hom_away (i : σ) :
    (coordinateSectionChartIso M k s hc f hf i).hom ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
    (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc := by
  rw [hf]
  simp only [coordinateSectionChartIso, Iso.trans_hom, Category.assoc, Proj.awayι,
    Iso.hom_inv_id_assoc, Scheme.Hom.preimageIso_hom_ι, Scheme.isoOfEq_hom_ι_assoc]

def coordinateSectionRingEquiv (i : σ) :
    Γ(X,SectionOpens.isoOpen (s i)) ≃+* MvPolynomial (ChartVariables i) K :=
  (SectionOpens.isoOpen (s i)).topIso.commRingCatIsoToRingEquiv.symm.trans
    ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).trans
      (polynomialChartEquiv i))

lemma coordinateSectionRingEquiv_coordinate (i j : σ) :
    coordinateSectionRingEquiv M k s hc f hf i
      ((SectionOpens.isoOpen (s i)).topIso.hom
        (coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))) =
      chartToPoly (R := K) i (chartCoordinate i j) := by
  have h := sectionFrame_coordinate i k s hc
    (coordinateSectionChartIso M k s hc f hf i).hom
    (coordinateSectionChartIso_hom_away M k s hc f hf i).symm j
  change coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) =
    (schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).symm
      (chartCoordinate i j) at h
  simp only [coordinateSectionRingEquiv, RingEquiv.trans_apply, h]
  change (polynomialChartEquiv i)
    ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i))
      ((SectionOpens.isoOpen (s i)).topIso.inv
        ((SectionOpens.isoOpen (s i)).topIso.hom
          ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).symm
            (chartCoordinate i j))))) = _
  rw [Iso.hom_inv_id_apply, RingEquiv.apply_symm_apply]
  rfl

lemma coordinateSectionRingEquiv_power_coordinate (n : ℕ) (i j : σ) :
    coordinateSectionRingEquiv M k s hc f hf i
      ((SectionOpens.isoOpen (s i)).topIso.hom
        (coefficient (coordinatePowerFrame (s i) n)
          (restrictSection (SectionOpens.isoOpen (s i)).ι (powerSection (s j) n)))) =
      chartToPoly (R := K) i (chartCoordinate i j) ^ n := by
  erw [coordinatePowerFrame_coefficient, map_pow, map_pow,
    coordinateSectionRingEquiv_coordinate]

variable [Fintype σ]

def coordinatePowerVertex (n : ℕ) (i : σ) :
    (schemeFreeOpen X (SectionOpens.isoOpen (s i)) ⟶ modulePow X M n) →+
      Laurent σ K n :=
  framedLaurentVertex _ (modulePow X M n) i n
    (coordinatePowerFrame (s i) n)
    (coordinateSectionRingEquiv M k s hc f hf i)

lemma coordinatePowerVertex_regular (n : ℕ) (i : σ)
    (b : schemeFreeOpen X (SectionOpens.isoOpen (s i)) ⟶ modulePow X M n) :
    RegularOn {i} (coordinatePowerVertex M k s hc f hf n i b) :=
  framedLaurentVertex_regular _ _ _ _ _ _ b

lemma coordinatePowerVertex_injective (n : ℕ) (i : σ) :
    Function.Injective (coordinatePowerVertex M k s hc f hf n i) :=
  framedLaurentVertex_injective _ _ _ _ _ _

lemma coordinatePowerVertex_surjective_regular (n : ℕ) (i : σ)
    (p : Laurent σ K n) (hp : RegularOn {i} p) :
    ∃ b, coordinatePowerVertex M k s hc f hf n i b = p :=
  framedLaurentVertex_surjective_regular _ _ _ _ _ _ p hp

end
end PiExponentSeshadri.Projective

end OAI
