import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.LineBundleTensor
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
open PiExponent.WeightedLocalLattice
open scoped BigOperators
universe u

namespace PiExponent.WeightedLocalSheaf

def monomialSheaf
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    [Fintype ι] (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) :
    (Spec (CommRingCat.of A)).Modules :=
  tilde (ModuleCat.of A (monomialLattice A x monomials))

def monomialFrame
    {A K : Type u} {ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    monomialSheaf (A := A) x monomials ≅ structureSheaf (Spec (CommRingCat.of A)) :=
  (tilde.functor (CommRingCat.of A)).mapIso
    (monomialLattice_rank_one (A := A) x monomials hzero).some.symm.toModuleIso ≪≫
      tildeSelf

def monomialLineBundle
    {A K : Type u} {ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    LineBundle (Spec (CommRingCat.of A)) where
  sheaf := monomialSheaf x monomials
  locallyRankOne _ := ⟨⊤, trivial, ⟨
    (Scheme.Modules.restrictFunctor (⊤ : (Spec (CommRingCat.of A)).Opens).ι).mapIso
      (monomialFrame x monomials hzero) ≪≫
        Scheme.Modules.restrictUnitIso (⊤ : (Spec (CommRingCat.of A)).Opens).ι⟩⟩

def monomialSectionMap
    {A K : Type*} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    [Fintype ι] (x : ι → Kˣ) (monomials : Finset (ι → ℕ))
    (a : ι → ℕ) (ha : a ∈ monomials) : A →ₗ[A] monomialLattice A x monomials where
  toFun c := ⟨c • ((∏ i, x i ^ a i : Kˣ) : K),
    Submodule.smul_mem _ c (Submodule.subset_span ⟨a, ha, rfl⟩)⟩
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]

def monomialSection
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    [Fintype ι] (x : ι → Kˣ) (monomials : Finset (ι → ℕ))
    (a : ι → ℕ) (ha : a ∈ monomials) :
    structureSheaf (Spec (CommRingCat.of A)) ⟶ monomialSheaf (A := A) x monomials :=
  tildeSelf.inv ≫ (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (monomialSectionMap x monomials a ha))

def generatedSheaf
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) : (Spec (CommRingCat.of A)).Modules :=
  tilde (ModuleCat.of A (generatedLattice A y s))

def generatedSectionMap
    {A K : Type*} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) :
    A →ₗ[A] generatedLattice A y s where
  toFun c := ⟨c • y a, Submodule.smul_mem _ c (Submodule.subset_span ⟨a, ha, rfl⟩)⟩
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]

theorem generatedSectionMap_bijective_of_span
    {A K : Type*} {ι : Type*} [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    Function.Bijective (generatedSectionMap (A := A) y s a ha) := by
  constructor
  · intro c d h
    have h' := congrArg (fun z : generatedLattice A y s => (z : K)) h
    change c • y a = d • y a at h'
    simp only [Algebra.smul_def] at h'
    exact IsFractionRing.injective A K (mul_right_cancel₀ hya h')
  · intro z
    have hz := hspan.le z.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨c, Subtype.ext hc⟩

def generatedSection
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) :
    structureSheaf (Spec (CommRingCat.of A)) ⟶ generatedSheaf (A := A) y s :=
  tildeSelf.inv ≫ (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (generatedSectionMap y s a ha))

theorem generatedSection_isIso_of_minimum
    {A K : Type u} {ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hmin : ∀ b ∈ s, CurveLocalOrder.fractionAddValuation A K (y a) ≤
      CurveLocalOrder.fractionAddValuation A K (y b)) :
    IsIso (generatedSection (A := A) y s a ha) := by
  let e : A ≃ₗ[A] generatedLattice A y s := LinearEquiv.ofBijective
    (generatedSectionMap (A := A) y s a ha)
    (generatedSectionMap_bijective_of_span y s a ha hya
      (generatedLattice_eq_span_of_minimum y s a ha hya hmin))
  exact (tildeSelf.symm ≪≫ (tilde.functor (CommRingCat.of A)).mapIso e.toModuleIso).isIso_hom

def generatedLineBundle
    {A K : Type u} {ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hmin : ∀ b ∈ s, CurveLocalOrder.fractionAddValuation A K (y a) ≤
      CurveLocalOrder.fractionAddValuation A K (y b)) :
    LineBundle (Spec (CommRingCat.of A)) := by
  letI := generatedSection_isIso_of_minimum y s a ha hya hmin
  refine ⟨generatedSheaf y s, fun p => ⟨⊤, trivial, ⟨?_⟩⟩⟩
  exact (Scheme.Modules.restrictFunctor (⊤ : (Spec (CommRingCat.of A)).Opens).ι).mapIso
    (asIso (generatedSection (A := A) y s a ha)).symm ≪≫
      Scheme.Modules.restrictUnitIso (⊤ : (Spec (CommRingCat.of A)).Opens).ι

end PiExponent.WeightedLocalSheaf

end

end OAI
