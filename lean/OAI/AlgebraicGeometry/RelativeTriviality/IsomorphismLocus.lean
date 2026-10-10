import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.ResidueIsomorphism

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeCech
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules
universe u
variable {X : Scheme.{u}} {F E : X.Modules} (φ : F ⟶ E)
def isoLocus : X.Opens :=
  ⨆ (U : X.Opens) (_ : ∀ V : X.Opens, V ≤ U → Function.Bijective (φ.app V)), U
lemma mem_isoLocus (x : X) : x ∈ isoLocus φ ↔
    ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U → Function.Bijective (φ.app V) := by
  simp only [isoLocus, Opens.mem_iSup]
  aesop
lemma isIso_of_local_bijective
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∀ V : X.Opens, V ≤ U → Function.Bijective (φ.app V)) : IsIso φ := by
  choose U hx hU using h
  have hc : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff]
    exact top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩)
  let ψ := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hp : IsIso ψ := by
    apply CategoryTheory.Sheaf.isIso_of_coversTop hc
    intro x
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hU x V.unop.left (leOfHom V.unop.hom)
  have : IsIso ((toPresheaf X).map φ) := by
    exact (sheafToPresheaf _ _).map_isIso ψ
  exact isIso_of_reflects_iso φ (toPresheaf X)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules
universe u
lemma isIso_restrict_of_range_in_isoLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {F E : Y.Modules} (φ : F ⟶ E)
    (h : ∀ x : X, f x ∈ isoLocus φ) : IsIso ((restrictFunctor f).map φ) := by
  apply isIso_of_local_bijective
  intro x
  obtain ⟨U, hx, hU⟩ := (mem_isoLocus φ (f x)).mp (h x)
  refine ⟨f ⁻¹ᵁ U, hx, ?_⟩
  intro V hV
  change Function.Bijective (φ.app (f ''ᵁ V))
  apply hU
  rintro y ⟨z, hz, rfl⟩
  exact hV hz
lemma isIso_pullback_isoLocus {X : Scheme.{u}} {F E : X.Modules} (φ : F ⟶ E) :
    IsIso ((pullback (isoLocus φ).ι).map φ) := by
  have := isIso_restrict_of_range_in_isoLocus (isoLocus φ).ι φ (fun x => x.property)
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback (isoLocus φ).ι) φ).mp inferInstance
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules
universe u
lemma isIso_pullback_of_range_in_isoLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F E : Y.Modules} (φ : F ⟶ E) (h : ∀ x : X, f x ∈ isoLocus φ) :
    IsIso ((pullback f).map φ) := by
  let U := isoLocus φ
  have hr : Set.range f ⊆ Set.range U.ι := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨f x, h x⟩, rfl⟩
  let g := IsOpenImmersion.lift U.ι f hr
  have hg : g ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  have := isIso_pullback_isoLocus φ
  have : IsIso (((pullback U.ι) ⋙ pullback g).map φ) :=
    Functor.map_isIso (pullback g) _
  rw [← hg]
  exact (NatIso.isIso_map_iff (pullbackComp g U.ι) φ).mp inferInstance
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules
universe u
lemma affine_field_point_mem_isoLocus {R : CommRingCat.{u}} {K : Type u} [Field K]
    {F E : (Spec R).Modules} [F.IsQuasicoherent] [E.IsQuasicoherent]
    [Module.Finite R (moduleSpecΓFunctor.obj F)]
    [Module.Flat R (moduleSpecΓFunctor.obj F)]
    [Module.FinitePresentation R (moduleSpecΓFunctor.obj E)]
    [Module.Flat R (moduleSpecΓFunctor.obj E)]
    (φ : F ⟶ E) (g : Spec (.of K) ⟶ Spec R)
    [IsIso ((pullback g).map φ)] : g default ∈ isoLocus φ := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective g
  let : Algebra R K := a.hom.toAlgebra
  have hbij := affine_baseChange_bijective_of_isIso_pullback K φ
  let p : PrimeSpectrum R := Spec.map a default
  have hp : p.asIdeal = RingHom.ker (algebraMap R K) := rfl
  have hres := residue_bijective_of_field_bijective (moduleSpecΓFunctor.map φ).hom
    p.asIdeal hp hbij
  obtain ⟨r, hr, hU⟩ := affine_exists_basicOpen_bijective φ p hres
  exact (mem_isoLocus φ p).mpr ⟨PrimeSpectrum.basicOpen r, hr, hU⟩
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules
universe u
lemma mem_isoLocus_of_mem_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {F E : Y.Modules} (φ : F ⟶ E) (x : X)
    (hx : x ∈ isoLocus ((restrictFunctor f).map φ)) : f x ∈ isoLocus φ := by
  obtain ⟨U, hxU, hU⟩ := (mem_isoLocus _ x).mp hx
  apply (mem_isoLocus φ (f x)).mpr
  refine ⟨f ''ᵁ U, ⟨x, hxU, rfl⟩, ?_⟩
  intro W hW
  have hpre : f ⁻¹ᵁ W ≤ U := by
    intro z hz
    obtain ⟨w, hw, he⟩ := hW hz
    exact f.isOpenEmbedding.injective he ▸ hw
  have he : f ''ᵁ (f ⁻¹ᵁ W) = W := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hy
      obtain ⟨z, hz, rfl⟩ := hW hy
      exact ⟨z, hy, rfl⟩
  have hh := hU (f ⁻¹ᵁ W) hpre
  change Function.Bijective (φ.app (f ''ᵁ (f ⁻¹ᵁ W))) at hh
  rwa [he] at hh
end

section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
lemma flat_affine_sections {R : CommRingCat.{u}} (E : (Spec R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType) :
    Module.Flat R (moduleSpecΓFunctor.obj E) := by
  have := flat_affine_restriction R (Spec R) E hE (𝟙 _)
  exact Module.Flat.of_linearEquiv
    (moduleSpecΓFunctor.mapIso (restrictFunctorId.app E)).toLinearEquiv.symm
lemma finitePresentation_affine_sections {R : CommRingCat.{u}} (E : (Spec R).Modules)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType) :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj E) := by
  have := finitePresentation_affine_restriction R (Spec R) E hE (𝟙 _)
  exact Module.FinitePresentation.of_equiv
    (moduleSpecΓFunctor.mapIso (restrictFunctorId.app E)).toLinearEquiv
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules
universe u
lemma field_point_mem_isoLocus {X : Scheme.{u}} {K : Type u} [Field K]
    {F E : X.Modules}
    (hF : ∃ q : F.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (φ : F ⟶ E) (g : Spec (.of K) ⟶ X)
    [IsIso ((pullback g).map φ)] : g default ∈ isoLocus φ := by
  obtain ⟨qF, hqF, htF⟩ := hF
  obtain ⟨qE, hqE, htE⟩ := hE
  let := hqF
  let := htF
  let := qF.isLocallyFree
  let := hqE
  let := htE
  let := qE.isLocallyFree
  have : F.IsQuasicoherent := qF.quasiCoherentData.isQuasicoherent
  have : E.IsQuasicoherent := qE.quasiCoherentData.isQuasicoherent
  obtain ⟨R, f, hf, y, hy⟩ := X.exists_Spec_apply_eq (g default)
  let := hf
  have hr : Set.range g ⊆ Set.range f := by
    rintro z ⟨t, rfl⟩
    refine ⟨y, ?_⟩
    simpa only [Subsingleton.elim t (default : Spec (.of K))] using hy
  let g' := IsOpenImmersion.lift f g hr
  have hg : g' ≫ f = g := IsOpenImmersion.lift_fac _ _ _
  have : IsIso ((pullback (g' ≫ f)).map φ) := by rw [hg]; infer_instance
  have : IsIso (((pullback f) ⋙ pullback g').map φ) :=
    (NatIso.isIso_map_iff (pullbackComp g' f) φ).mpr inferInstance
  have : IsIso ((pullback g').map ((restrictFunctor f).map φ)) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight (restrictFunctorIsoPullback f) (pullback g')) φ).mpr
      inferInstance
  have := flat_affine_restriction R X F ⟨qF, hqF, htF⟩ f
  have := flat_affine_restriction R X E ⟨qE, hqE, htE⟩ f
  have := finitePresentation_affine_restriction R X F ⟨qF, hqF, htF⟩ f
  have := finitePresentation_affine_restriction R X E ⟨qE, hqE, htE⟩ f
  have hm := affine_field_point_mem_isoLocus ((restrictFunctor f).map φ) g'
  have hn := mem_isoLocus_of_mem_restrict f φ (g' default) hm
  convert hn using 1
  exact congrArg (fun h : Spec (.of K) ⟶ X => h default) hg.symm
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
 

lemma exists_basicOpen_preimage_le {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [UniversallyClosed f] (p : PrimeSpectrum R)
    (U : X.Opens) (hp : ∀ x : X, f x = p → x ∈ U) :
    ∃ r : R, r ∉ p.asIdeal ∧ f ⁻¹ᵁ (PrimeSpectrum.basicOpen r) ≤ U := by
  let V : (Spec R).Opens := ⟨(f '' (U : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  have hpV : p ∈ V := by
    rintro ⟨x, hx, hxp⟩
    exact hx (hp x hxp)
  obtain ⟨W, ⟨r, rfl⟩, hr, hV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpV V.isOpen
  refine ⟨r, hr, ?_⟩
  intro x hx
  by_contra hn
  exact hV hx ⟨x, hn, rfl⟩
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open Scheme.Modules
universe u
lemma residueSpecMap_apply (R : CommRingCat.{u}) (p : PrimeSpectrum R)
    (t : Spec (.of p.asIdeal.ResidueField)) :
    Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)) t = p := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R p.asIdeal.ResidueField) t.asIdeal = p.asIdeal
  rw [Subsingleton.elim t (⊥ : PrimeSpectrum p.asIdeal.ResidueField)]
  exact Ideal.ker_algebraMap_residueField _
lemma fiber_mem_isoLocus {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) {F E : X.Modules}
    (hF : ∃ q : F.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (p : PrimeSpectrum R) (φ : F ⟶ E)
    [IsIso ((Scheme.Modules.pullback (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).map φ)]
    (x : X) (hx : f x = p) : x ∈ isoLocus φ := by
  let k := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
  let P := Limits.pullback f k
  have hx' : x ∈ Set.range (Limits.pullback.fst f k) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨default, (residueSpecMap_apply R p _).trans hx.symm⟩
  obtain ⟨y, hy⟩ := hx'
  let g : Spec (P.residueField y) ⟶ X := P.fromSpecResidueField y ≫ Limits.pullback.fst f k
  have : IsIso ((Scheme.Modules.pullback (Limits.pullback.fst f k)).map φ) := inferInstance
  have hpb : IsIso ((Scheme.Modules.pullback (P.fromSpecResidueField y)).map
      ((Scheme.Modules.pullback (Limits.pullback.fst f k)).map φ)) :=
    Functor.map_isIso (Scheme.Modules.pullback (P.fromSpecResidueField y)) _
  have : IsIso ((Scheme.Modules.pullback g).map φ) :=
    (NatIso.isIso_map_iff (pullbackComp _ _) φ).mp hpb
  have hh := field_point_mem_isoLocus (K := P.residueField y) hF hE φ g
  have hgpt (t : Spec (P.residueField y)) : g t = x := by
    change (Limits.pullback.fst f k) ((P.fromSpecResidueField y) t) = x
    rw [Scheme.fromSpecResidueField_apply]
    exact hy
  exact Eq.mp (congrArg (fun z : X => z ∈ isoLocus φ) (hgpt _)) hh
lemma isIso_near_fiber_proper {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [UniversallyClosed f] {F E : X.Modules}
    (hF : ∃ q : F.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (hE : ∃ q : E.LocalGeneratorsData, q.IsLocallyFreeData ∧ q.IsFiniteType)
    (p : PrimeSpectrum R) (φ : F ⟶ E)
    [IsIso ((Scheme.Modules.pullback (Limits.pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))))).map φ)] :
    ∃ r : R, r ∉ p.asIdeal ∧ IsIso ((Scheme.Modules.pullback
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away r)))))).map φ) := by
  obtain ⟨r, hr, hU⟩ := exists_basicOpen_preimage_le f p (isoLocus φ)
    (fiber_mem_isoLocus f hF hE p φ)
  refine ⟨r, hr, isIso_pullback_of_range_in_isoLocus _ φ ?_⟩
  intro x
  apply hU
  have hx : f (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away r)))) x) ∈
      Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    let a := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
    refine ⟨Limits.pullback.snd f a x, ?_⟩
    exact congrArg (fun h : Limits.pullback f a ⟶ Spec R => h x)
      (Limits.pullback.condition (f := f) (g := a)).symm
  rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at hx
end CampanaPeternellSix.RelativeCech

end

end OAI
