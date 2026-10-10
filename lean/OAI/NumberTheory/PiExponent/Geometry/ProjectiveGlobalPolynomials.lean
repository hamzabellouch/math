import OAI.NumberTheory.PiExponent.Cohomology.CechZero
import OAI.NumberTheory.PiExponent.Cohomology.GradedH0
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveCoordinateAcyclicity
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomialAlgebra
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveRepresentedCoefficient
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveVertexCompatibility

namespace OAI

namespace PiExponent.ProjectiveGlobalPolynomials
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open GeometrySupport ProjectiveTwistCech ProjectiveMonomialCech

variable {X : Scheme.{0}} {σ R : Type} [CommRing R] [Fintype σ]
variable {U : σ → X.Opens} {M : X.Modules} {n : ℕ}

private abbrev schemeFreeOpen (X : Scheme.{0}) (V : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf V

def globalCochain (U : σ → X.Opens) (M : X.Modules)
    (b : structureSheaf X ⟶ M) : CechHigher.Cochain X.ringCatSheaf U M 0 :=
  CechHigher.augmentation X.ringCatSheaf U M ⊤ (fun _ => le_top)
    ((PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b)

def globalLaurent (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ProjectiveMonomialCechHigher.Cochain σ (Laurent σ R (n : ℤ)) 0 :=
  P.toLaurent (globalCochain U M b)

lemma globalLaurent_closed (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ProjectiveMonomialCechHigher.differential (globalLaurent P b) = 0 := by
  rw [globalLaurent, ← P.toLaurent_differential]
  rw [globalCochain]
  erw [CechHigher.augmentation_closed]
  funext t
  exact map_zero _

theorem existsUnique_polynomial [Nonempty σ] (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ t, GradedH0.polynomialLaurent n p = globalLaurent P b t := by
  exact GradedH0.zeroth_cocycle_unique_homogeneous_polynomial n (globalLaurent P b)
    (fun t => P.regular 0 t _) (globalLaurent_closed P b)

lemma globalLaurent_injective (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (hcover : (⨆ i, U i) = ⊤) : Function.Injective (globalLaurent P) := by
  intro b c h
  apply (cancel_epi (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom).mp
  apply CechZero.augmentation_injective X.ringCatSheaf U M ⊤ (fun _ => le_top)
    (by rw [hcover])
  funext t
  apply P.injective 0 t
  exact congrFun h t

theorem existsUnique_section (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (hcover : (⨆ i, U i) = ⊤) (p : MvPolynomial.homogeneousSubmodule σ R n) :
    ∃! b : structureSheaf X ⟶ M,
      ∀ t, globalLaurent P b t = GradedH0.polynomialLaurent n p := by
  have hreg (t : Fin 1 → σ) :
      RegularOn (Set.range t) (GradedH0.polynomialLaurent n p) := by
    intro a ha i hi
    exact False.elim (GradedH0.polynomialLaurent_regular n p a ha i hi)
  choose c hc using fun t => P.surjective 0 t (GradedH0.polynomialLaurent n p) (hreg t)
  have hcoeff : P.toLaurent c = fun _ => GradedH0.polynomialLaurent n p := funext hc
  have hconst : ProjectiveMonomialCechHigher.differential
      (fun _ : Fin 1 → σ => GradedH0.polynomialLaurent n p) = 0 := by
    funext t
    change (∑ j : Fin 2, (-1 : ℤ) ^ j.val • GradedH0.polynomialLaurent n p) = 0
    rw [Fin.sum_univ_two]
    simp
  have hclosed : CechHigher.differential X.ringCatSheaf U M c =
      fun t => (0 : schemeFreeOpen X (CechHigher.intersection U t) ⟶ M) := by
    funext t
    apply P.injective 1 t
    have h := congrFun (P.toLaurent_differential c) t
    rw [hcoeff, hconst] at h
    exact h.trans (P.coefficient 1 t).map_zero.symm
  obtain ⟨b, hb⟩ := CechZero.augmentation_exists X.ringCatSheaf U M ⊤ (fun _ => le_top)
    (by rw [hcover]) c hclosed
  let s : structureSheaf X ⟶ M :=
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).inv ≫ b
  have hs : globalLaurent P s = fun _ => GradedH0.polynomialLaurent n p := by
    unfold globalLaurent globalCochain s
    erw [Iso.hom_inv_id_assoc, hb]
    exact hcoeff
  refine ⟨s, fun t => congrFun hs t, ?_⟩
  intro z hz
  apply globalLaurent_injective P hcover
  exact (funext hz).trans hs.symm

def representedRestriction (V : X.Opens) (N : X.Modules) (b : structureSheaf X ⟶ N) :
    freeOpen X.ringCatSheaf V ⟶ N :=
  freeOpenMap X.ringCatSheaf (homOfLE (show V ≤ ⊤ from le_top)) ≫
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b

omit [Fintype σ] in
lemma globalCochain_restrict (U : σ → X.Opens) (N : X.Modules)
    (b : structureSheaf X ⟶ N) (t : Fin 1 → σ) :
    globalCochain U N b t = freeOpenMap X.ringCatSheaf
      (homOfLE (iInf_le (fun j => U (t j)) 0)) ≫ representedRestriction (U (t 0)) N b := by
  change freeOpenMap X.ringCatSheaf _ ≫ _ = freeOpenMap X.ringCatSheaf _ ≫
    (freeOpenMap X.ringCatSheaf _ ≫ _)
  simp only [freeOpenMap]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp]
  rfl

open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open GeometrySupport.ProjectiveCoordinateAcyclicity GeometrySupport.ProjectiveTupleCharts
open GeometrySupport.ProjectiveLaurentVertex GeometrySupport.ProjectiveGlobalPolynomialAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra
variable (L : X.Modules) (s : σ → (structureSheaf X ⟶ L)) (k : R →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade R σ)) (hf : sectionsMorphism k s hc = f.hom)

def coordinateChartPolynomial (n : ℕ) (i : σ)
    (b : structureSheaf X ⟶ modulePow X L n) : MvPolynomial (ChartVariables i) R :=
  framedHomRingEquiv (PiExponentSeshadri.SectionOpens.isoOpen (s i)) (modulePow X L n)
    (coordinatePowerFrame (s i) n) (coordinateSectionRingEquiv L k s hc f hf i)
    (representedRestriction (PiExponentSeshadri.SectionOpens.isoOpen (s i)) _ b)

omit [Fintype σ] in

lemma coordinateChartPolynomial_coefficient (n : ℕ) (i : σ)
    (b : structureSheaf X ⟶ modulePow X L n) :
    coordinateChartPolynomial L s k hc f hf n i b =
      coordinateSectionRingEquiv L k s hc f hf i
        ((PiExponentSeshadri.SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (coordinatePowerFrame (s i) n)
            (restrictSection (PiExponentSeshadri.SectionOpens.isoOpen (s i)).ι b))) := by
  change coordinateSectionRingEquiv L k s hc f hf i
    (framedHomCoefficientsEquiv _ _ (coordinatePowerFrame (s i) n)
      (freeOpenMap X.ringCatSheaf (homOfLE le_top) ≫
        (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b)) = _
  rw [framedHomCoefficientsEquiv_globalSection]

lemma coordinate_globalLaurent_vertex (n : ℕ)
    (b : structureSheaf X ⟶ modulePow X L n) (t : Fin 1 → σ) :
    globalLaurent (coordinateLaurentCechPresentation L s k hc f hf n) b t =
      vertexLaurent (t 0) (n : ℤ) (coordinateChartPolynomial L s k hc f hf n (t 0) b) := by
  change coordinateTupleCoefficient L s k hc f hf n 0 t
    (globalCochain (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) _ b t) = _
  rw [globalCochain_restrict]
  exact coordinateTupleCoefficient_restrictVertex L s k hc f hf n 0 t _

theorem coordinate_existsUnique_polynomial [Nonempty σ] (n : ℕ)
    (b : structureSheaf X ⟶ modulePow X L n) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ i, dehomogenize i p.val = coordinateChartPolynomial L s k hc f hf n i b := by
  obtain ⟨p, hp, hu⟩ := existsUnique_polynomial
    (coordinateLaurentCechPresentation L s k hc f hf n) b
  refine ⟨p, ?_, ?_⟩
  · intro i
    apply vertexLaurent_injective i (n : ℤ)
    rw [vertexLaurent_dehomogenize]
    exact (hp (fun _ => i)).trans (coordinate_globalLaurent_vertex L s k hc f hf n b _)
  · intro q hq
    apply hu q
    intro t
    calc
      GradedH0.polynomialLaurent n q = vertexLaurent (t 0) (n : ℤ)
          (dehomogenize (t 0) q.val) := (vertexLaurent_dehomogenize (t 0) n q).symm
      _ = vertexLaurent (t 0) (n : ℤ)
          (coordinateChartPolynomial L s k hc f hf n (t 0) b) := congrArg _ (hq (t 0))
      _ = _ := (coordinate_globalLaurent_vertex L s k hc f hf n b t).symm

theorem coordinate_existsUnique_section (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ R n) :
    ∃! b : structureSheaf X ⟶ modulePow X L n,
      ∀ i, dehomogenize i p.val = coordinateChartPolynomial L s k hc f hf n i b := by
  obtain ⟨b, hb, hu⟩ := existsUnique_section
    (coordinateLaurentCechPresentation L s k hc f hf n) hc p
  refine ⟨b, ?_, ?_⟩
  · intro i
    apply vertexLaurent_injective i (n : ℤ)
    rw [vertexLaurent_dehomogenize]
    exact (hb (fun _ => i)).symm.trans (coordinate_globalLaurent_vertex L s k hc f hf n b _)
  · intro z hz
    apply hu z
    intro t
    calc
      globalLaurent (coordinateLaurentCechPresentation L s k hc f hf n) z t =
          vertexLaurent (t 0) (n : ℤ) (coordinateChartPolynomial L s k hc f hf n (t 0) z) :=
        coordinate_globalLaurent_vertex L s k hc f hf n z t
      _ = vertexLaurent (t 0) (n : ℤ) (dehomogenize (t 0) p.val) := congrArg _ (hz (t 0)).symm
      _ = _ := vertexLaurent_dehomogenize (t 0) n p


end
end PiExponent.ProjectiveGlobalPolynomials

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveGlobalPolynomials
attribute [local irreducible] lineBundle coordinateSection scalars sectionsMorphism
variable {R σ : Type} [CommRing R] [Fintype σ]

def globalSectionChartPolynomial (n : ℕ) (i : σ)
    (b : structureSheaf (projectiveSpace R σ) ⟶
      modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) :
    MvPolynomial (ChartVariables i) R :=
  coordinateChartPolynomial (X := projectiveSpace R σ) (R := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf (coordinateSection (R := R) (σ := σ))
    (scalars (R := R) (σ := σ)) (coordinateSection_cover (R := R) (σ := σ))
    (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n i b

theorem globalSection_homogeneous_polynomial [Nonempty σ] (n : ℕ)
    (b : structureSheaf (projectiveSpace R σ) ⟶
      modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ i, dehomogenize i p.val = globalSectionChartPolynomial n i b := by
  exact coordinate_existsUnique_polynomial (X := projectiveSpace R σ) (R := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf (coordinateSection (R := R) (σ := σ))
    (scalars (R := R) (σ := σ)) (coordinateSection_cover (R := R) (σ := σ))
    (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n b

theorem homogeneousPolynomial_globalSection (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ R n) :
    ∃! b : structureSheaf (projectiveSpace R σ) ⟶
      modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n,
      ∀ i, dehomogenize i p.val = globalSectionChartPolynomial n i b := by
  exact coordinate_existsUnique_section (X := projectiveSpace R σ) (R := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf (coordinateSection (R := R) (σ := σ))
    (scalars (R := R) (σ := σ)) (coordinateSection_cover (R := R) (σ := σ))
    (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n p

end
end PiExponent.ProjectiveO1

end OAI
