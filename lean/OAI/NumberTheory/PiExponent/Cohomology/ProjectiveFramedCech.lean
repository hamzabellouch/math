import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (N : X.Modules)
variable (e : ∀ i, N.restrict (SectionOpens.isoOpen (s i)).ι ≅
  structureSheaf (SectionOpens.isoOpen (s i)).toScheme) (d : ℤ)

private abbrev schemeFreeOpen (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

def coordinateFramedOverlap (i : σ) (a : Finset (ChartVariables i)) :
    (schemeFreeOpen (coordinateFiniteOpen M s i a) ⟶ N) →+ Laurent σ K d :=
  framedLaurentOverlap _ N i d a (restrictOpenFrame inf_le_left (e i))
    (coordinateFiniteRingEquiv M s k hc f hf i a)

lemma coordinateFramedOverlap_injective (i : σ) (a : Finset (ChartVariables i)) :
    Function.Injective (coordinateFramedOverlap M s k hc f hf N e d i a) :=
  framedLaurentOverlap_injective _ _ _ _ _ _ _

lemma coordinateFramedOverlap_regular (i : σ) (a : Finset (ChartVariables i))
    (b : schemeFreeOpen (coordinateFiniteOpen M s i a) ⟶ N) :
    RegularOn ({i} ∪ Subtype.val '' (a : Set (ChartVariables i)))
      (coordinateFramedOverlap M s k hc f hf N e d i a b) :=
  framedLaurentOverlap_regular _ _ _ _ _ _ _ b

lemma coordinateFramedOverlap_surjective (i : σ) (a : Finset (ChartVariables i))
    (p : Laurent σ K d) (hp : RegularOn ({i} ∪ Subtype.val '' (a : Set (ChartVariables i))) p) :
    ∃ b, coordinateFramedOverlap M s k hc f hf N e d i a b = p :=
  framedLaurentOverlap_surjective_regular _ _ _ _ _ _ _ p hp

attribute [local irreducible] coordinateFramedOverlap

def coordinateFramedTuple (q : ℕ) (t : Fin (q + 1) → σ) :
    (schemeFreeOpen
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) →+
      Laurent σ K d :=
  (coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).toAddMonoidHom

lemma coordinateFramedTuple_injective (q : ℕ) (t : Fin (q + 1) → σ) :
    Function.Injective (coordinateFramedTuple M s k hc f hf N e d q t) := by
  intro b c h
  apply (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).injective
  apply coordinateFramedOverlap_injective M s k hc f hf N e d (t 0) (tupleVariables t 0)
  exact h

lemma coordinateFramedTuple_regular (q : ℕ) (t : Fin (q + 1) → σ)
    (b : schemeFreeOpen
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) :
    RegularOn (Set.range t) (coordinateFramedTuple M s k hc f hf N e d q t b) := by
  have h := coordinateFramedOverlap_regular M s k hc f hf N e d (t 0) (tupleVariables t 0)
    (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) b)
  change RegularOn (Set.range t) ((coordinateFramedOverlap M s k hc f hf N e d (t 0)
    (tupleVariables t 0)) ((freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)) b))
  simpa only [tupleVariables_support] using h

lemma coordinateFramedTuple_surjective (q : ℕ) (t : Fin (q + 1) → σ)
    (p : Laurent σ K d) (hp : RegularOn (Set.range t) p) :
    ∃ b, coordinateFramedTuple M s k hc f hf N e d q t b = p := by
  obtain ⟨b, hb⟩ := coordinateFramedOverlap_surjective M s k hc f hf N e d (t 0)
    (tupleVariables t 0) p (by simpa only [tupleVariables_support] using hp)
  refine ⟨(freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).symm b, ?_⟩
  change coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)
    ((freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0))
      ((freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).symm b)) = p
  rw [AddEquiv.apply_symm_apply]
  exact hb

def coordinateFramedLaurentPresentation
    (hres : ∀ i j (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
      (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
      (z : schemeFreeOpen (coordinateFiniteOpen M s i a) ⟶ N),
      coordinateFramedOverlap M s k hc f hf N e d j b
        (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      coordinateFramedOverlap M s k hc f hf N e d i a z) :
    PiExponent.ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => SectionOpens.isoOpen (s i)) N d where
  coefficient := coordinateFramedTuple M s k hc f hf N e d
  injective := coordinateFramedTuple_injective M s k hc f hf N e d
  regular := coordinateFramedTuple_regular M s k hc f hf N e d
  surjective := coordinateFramedTuple_surjective M s k hc f hf N e d
  restriction q t j z := by
    change coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)
      (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)
        (freeOpenMap X.ringCatSheaf (homOfLE
          (PiExponent.GeometrySupport.CechHigher.faceLE (fun i => SectionOpens.isoOpen (s i)) t j)) ≫ z)) =
      coordinateFramedOverlap M s k hc f hf N e d ((t ∘ j.succAbove) 0)
        (tupleVariables (t ∘ j.succAbove) 0)
        (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s (t ∘ j.succAbove) 0) z)
    erw [freeOpenHomCongr_restrict]
    exact hres _ _ _ _ _ _

end
end PiExponentSeshadri.Projective

end OAI
