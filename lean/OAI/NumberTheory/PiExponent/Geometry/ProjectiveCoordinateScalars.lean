import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveFramedCech
import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque

private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} (U : X.Opens) (M : X.Modules)
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen :
    Module Γ(X,⊤) (schemeFreeOpen X U ⟶ M) :=
  sheafHomModule X _ M

lemma freeOpenAddEquiv_smul (r : Γ(X,⊤)) (b : schemeFreeOpen X U ⟶ M) :
    freeOpenAddEquiv U M (r • b) = restrictScalar X U r • freeOpenAddEquiv U M b := by
  rfl

lemma framedHomCoefficientsEquiv_smul
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,⊤)) (b : schemeFreeOpen X U ⟶ M) :
    framedHomCoefficientsEquiv U M e (r • b) =
      restrictScalar X U r * framedHomCoefficientsEquiv U M e b := by
  change framedCoefficientsEquiv U M e (freeOpenAddEquiv U M (r • b)) = _
  rw [freeOpenAddEquiv_smul, framedCoefficientsEquiv_smul]
  rfl
end PiExponentSeshadri.ProjectiveChartSections

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.ProjectiveMonomialCech
variable {K σ : Type} [CommRing K] [Fintype σ]

lemma groupAlgebraToLaurent_smul (i : σ) (d : ℤ) (c : K)
    (z : chartGroupAlgebra (R := K) i) :
    groupAlgebraToLaurent i d (c • z) = c • groupAlgebraToLaurent i d z := by
  ext a
  rfl

lemma overlapLaurent_constant_mul (i : σ) (d : ℤ) (a : Finset {j : σ // j ≠ i})
    (c : K) (z : Localization.Away (chartProduct (R := K) i a)) :
    overlapLaurent i d a (algebraMap (MvPolynomial {j : σ // j ≠ i} K) _ (MvPolynomial.C c) * z) =
      c • overlapLaurent i d a z := by
  change groupAlgebraToLaurent i d
    (overlapToGroupAlgebra i a (algebraMap (MvPolynomial {j : σ // j ≠ i} K) _ (MvPolynomial.C c) * z)) = _
  rw [map_mul, overlapToGroupAlgebra_base]
  have hc : polynomialToGroupAlgebra i (MvPolynomial.C c) =
      AddMonoidAlgebra.single 0 c := by
    change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single 0 c) = _
    rw [AddMonoidAlgebra.mapDomain_single, map_zero]
  have hs (z' : chartGroupAlgebra (R := K) i) :
      AddMonoidAlgebra.single 0 c * z' = c • z' := by
    ext a'
    simp only [AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hc, hs, groupAlgebraToLaurent_smul]
  rfl
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

namespace PiExponentSeshadri.Projective
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
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen
    (U : X.Opens) : Module Γ(X,⊤) (schemeFreeOpen X U ⟶ N) :=
  sheafHomModule X _ N
variable (e : ∀ i, N.restrict (SectionOpens.isoOpen (s i)).ι ≅
  structureSheaf (SectionOpens.isoOpen (s i)).toScheme) (d : ℤ)

lemma coordinateFramedOverlap_smul (i : σ) (a : Finset (ChartVariables i))
    (c : K) (b : schemeFreeOpen X (coordinateFiniteOpen M s i a) ⟶ N) :
    coordinateFramedOverlap M s k hc f hf N e d i a ((k c) • b) =
      c • coordinateFramedOverlap M s k hc f hf N e d i a b := by
  let g := framedHomCoefficientsEquiv (coordinateFiniteOpen M s i a) N
    (restrictOpenFrame inf_le_left (e i))
  let r := coordinateFiniteRingEquiv M s k hc f hf i a
  change overlapLaurent i d a (r (g ((k c) • b))) = c • overlapLaurent i d a (r (g b))
  have hs : g ((k c) • b) = restrictScalar X (coordinateFiniteOpen M s i a) (k c) * g b :=
    framedHomCoefficientsEquiv_smul (coordinateFiniteOpen M s i a) N
      (restrictOpenFrame inf_le_left (e i)) (k c) b
  have hr : r (restrictScalar X (coordinateFiniteOpen M s i a) (k c)) =
      algebraMap _ _ (MvPolynomial.C c) :=
    coordinateFiniteRingEquiv_constant M s k hc f hf i a c
  rw [hs, map_mul, hr]
  exact overlapLaurent_constant_mul i d a c _

attribute [local irreducible] coordinateFramedOverlap
lemma coordinateFramedTuple_smul (q : ℕ) (t : Fin (q + 1) → σ)
    (c : K) (b : schemeFreeOpen X
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) :
    coordinateFramedTuple M s k hc f hf N e d q t ((k c) • b) =
      c • coordinateFramedTuple M s k hc f hf N e d q t b := by
  have htrans : freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) ((k c) • b) =
      (k c) • freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) b := by
    change freeOpenMap X.ringCatSheaf (eqToHom (coordinateFiniteOpen_tuple M s t 0)) ≫
      ((k c) • b) = _
    exact Linear.comp_smul (C := X.Modules) _ _ _ _ (k c) b
  change coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)
    (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) ((k c) • b)) = _
  rw [htrans]
  exact coordinateFramedOverlap_smul M s k hc f hf N e d _ _ c _

end PiExponentSeshadri.Projective

end

end OAI
