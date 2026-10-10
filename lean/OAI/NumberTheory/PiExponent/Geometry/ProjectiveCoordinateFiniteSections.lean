import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateSections

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra

def isoPreimageSectionRingEquiv {X Y : Scheme} (f : X ≅ Y) (V : Y.Opens) :
    Γ(X,f.hom ⁻¹ᵁ V) ≃+* Γ(Y,V) :=
  ((IsOpenImmersion.ΓIso f.hom V) ≪≫
    Y.presheaf.mapIso (eqToIso (show V = f.hom.opensRange ⊓ V by rw [Scheme.Hom.opensRange_of_isIso, top_inf_eq])).op).commRingCatIsoToRingEquiv

private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M))

def coordinateFiniteOpen (i : σ) (a : Finset (ChartVariables i)) : X.Opens :=
  SectionOpens.isoOpen (s i) ⊓ a.inf (fun j => SectionOpens.isoOpen (s j.val))

variable (k : K →+* Γ(X,⊤)) (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
include hf

lemma coordinateFiniteOpen_eq_preimage (i : σ) (a : Finset (ChartVariables i)) :
    coordinateFiniteOpen M s i a = f.hom ⁻¹ᵁ
      (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ⊓
        a.inf (fun j => Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X j.val))) := by
  classical
  unfold coordinateFiniteOpen
  rw [Scheme.Hom.preimage_inf, ← sectionOpen_eq_coordinate_preimage M k s hc f hf i]
  congr 1
  induction a using Finset.induction_on with
  | empty => simp
  | @insert j a hj ih =>
    rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf,
      ← sectionOpen_eq_coordinate_preimage M k s hc f hf j.val, ih]

def coordinateFiniteRingEquiv (i : σ) (a : Finset (ChartVariables i)) :
    Γ(X,coordinateFiniteOpen M s i a) ≃+*
      Localization.Away (chartProduct (R := K) i a) :=
  (X.presheaf.mapIso (eqToIso
    (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).symm).op).commRingCatIsoToRingEquiv.trans
      ((isoPreimageSectionRingEquiv f _).trans (chartVariableOverlapRingEquiv i a))

variable [Fintype σ]

def coordinatePowerOverlap (n : ℕ) (i : σ) (a : Finset (ChartVariables i)) :
    (schemeFreeOpen X (coordinateFiniteOpen M s i a) ⟶ modulePow X M n) →+
      Laurent σ K n :=
  framedLaurentOverlap _ (modulePow X M n) i n a
    (restrictOpenFrame (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left)
      (coordinatePowerFrame (s i) n))
    (coordinateFiniteRingEquiv M s k hc f hf i a)

lemma coordinatePowerOverlap_injective (n : ℕ) (i : σ) (a : Finset (ChartVariables i)) :
    Function.Injective (coordinatePowerOverlap M s k hc f hf n i a) :=
  framedLaurentOverlap_injective _ _ _ _ _ _ _

lemma coordinatePowerOverlap_regular (n : ℕ) (i : σ) (a : Finset (ChartVariables i))
    (b : schemeFreeOpen X (coordinateFiniteOpen M s i a) ⟶ modulePow X M n) :
    RegularOn ({i} ∪ (Subtype.val '' (a : Set (ChartVariables i))))
      (coordinatePowerOverlap M s k hc f hf n i a b) :=
  framedLaurentOverlap_regular _ _ _ _ _ _ _ b

lemma coordinatePowerOverlap_surjective_regular (n : ℕ) (i : σ) (a : Finset (ChartVariables i))
    (p : Laurent σ K n)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (a : Set (ChartVariables i)))) p) :
    ∃ b, coordinatePowerOverlap M s k hc f hf n i a b = p :=
  framedLaurentOverlap_surjective_regular _ _ _ _ _ _ _ p hp

end
end PiExponentSeshadri.Projective

end OAI
