import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CanonicalExistence

namespace OAI

/-! Birational Extension. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
universe u

theorem extend_generic_section
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [IsProper f]
    (y : Y) [ValuationRing (Y.presheaf.stalk y)]
    (g : Spec Y.functionField ⟶ X)
    (hg : g ≫ f = Y.fromSpecStalk (genericPoint Y)) :
    ∃ (U : Y.Opens) (_ : y ∈ U) (s : U.toScheme ⟶ X), s ≫ f = U.ι := by
  have hv : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hw : g ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk y) Y.functionField)) ≫
        Y.fromSpecStalk y := by
    rw [hg]
    exact (Y.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec Y).specializes trivial)).symm
  obtain ⟨l, _, hl⟩ := (hv {
    R := Y.presheaf.stalk y
    commRing := inferInstanceAs (CommRing (Y.presheaf.stalk y))
    domain := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
    K := Y.functionField
    i₁ := g
    i₂ := Y.fromSpecStalk y
    commSq := ⟨hw⟩ }).exists_lift
  obtain ⟨U, hyU, s, _, hs⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f l (by simpa using hl)
  exact ⟨U, hyU, s, by simpa using hs⟩

theorem isIso_restrict_of_dominant_section
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) [IsSeparated f]
    (U : Y.Opens) (s : U.toScheme ⟶ X) [IsDominant s]
    (hs : s ≫ f = U.ι) : IsIso (f ∣_ U) := by
  have hsub : Set.range s ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨s z, ?_⟩, rfl⟩
    change f (s z) ∈ U
    rw [← Scheme.Hom.comp_apply, hs]
    exact z.2
  let t := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι s hsub
  have ht : t ≫ (f ⁻¹ᵁ U).ι = s := IsOpenImmersion.lift_fac _ _ _
  have htf : t ≫ (f ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ht, hs,
      Category.id_comp]
  have : IsDominant (t ≫ (f ⁻¹ᵁ U).ι) := ht ▸ inferInstance
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t (f ⁻¹ᵁ U).ι
  have : IsClosedImmersion (t ≫ (f ∣_ U)) := htf ▸ inferInstance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t (f ∣_ U)
  have : Surjective t :=
    surjective_of_isDominant_of_isClosed_range t t.isClosedEmbedding.isClosed_range
  have : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  have heq : (f ∣_ U) = inv t := by
    calc
      (f ∣_ U) = (inv t ≫ t) ≫ (f ∣_ U) := by simp
      _ = inv t := by rw [Category.assoc, htf, Category.comp_id]
  rw [heq]
  infer_instance

theorem isIso_near_valuation_of_generic_section
    {X Y : Scheme.{u}} [IsReduced X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] (y : Y)
    [ValuationRing (Y.presheaf.stalk y)]
    (g : Spec Y.functionField ⟶ X) [IsDominant g]
    (hg : g ≫ f = Y.fromSpecStalk (genericPoint Y)) :
    ∃ (U : Y.Opens), y ∈ U ∧ IsIso (f ∣_ U) := by
  have hv : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let a := Spec.map (CommRingCat.ofHom
    (algebraMap (Y.presheaf.stalk y) Y.functionField))
  have hw : g ≫ f = a ≫ Y.fromSpecStalk y := by
    rw [hg]
    exact (Y.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec Y).specializes trivial)).symm
  obtain ⟨l, hl₁, hl₂⟩ := (hv {
    R := Y.presheaf.stalk y
    commRing := inferInstanceAs (CommRing (Y.presheaf.stalk y))
    domain := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
    K := Y.functionField
    i₁ := g
    i₂ := Y.fromSpecStalk y
    commSq := ⟨hw⟩ }).exists_lift
  obtain ⟨U, hyU, s, hls, hs⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f l (by simpa using hl₂)
  have hfactor : (a ≫ U.fromSpecStalkOfMem y hyU) ≫ s = g := by
    rw [Category.assoc, ← hls]
    exact hl₁
  have : IsDominant ((a ≫ U.fromSpecStalkOfMem y hyU) ≫ s) :=
    hfactor ▸ inferInstance
  have : IsDominant s := IsDominant.of_comp (a ≫ U.fromSpecStalkOfMem y hyU) s
  exact ⟨U, hyU, isIso_restrict_of_dominant_section f U s (by simpa using hs)⟩

theorem isIso_near_codim_one_of_proper_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (φ : X.PartialIso Y)
    (hφ : φ.IsOver f (𝟙 Y)) (y : Y) (hy : Order.coheight y = 1)
    [IsIntegrallyClosed (Y.presheaf.stalk y)] :
    ∃ (U : Y.Opens), y ∈ U ∧ IsIso (f ∣_ U) := by
  have hd : ringKrullDim (Y.presheaf.stalk y) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hy]; rfl
  have hnf : ¬ IsField (Y.presheaf.stalk y) :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hd).1
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le hy.le
  have : Ring.DimensionLEOne (Y.presheaf.stalk y) :=
    ⟨fun {I} hI hprime =>
      Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance I hI hprime⟩
  have : IsDedekindDomain (Y.presheaf.stalk y) := {}
  have : IsDiscreteValuationRing (Y.presheaf.stalk y) :=
    ((IsDiscreteValuationRing.TFAE (Y.presheaf.stalk y) hnf).out 3 1).mp
      (show IsDedekindDomain (Y.presheaf.stalk y) from inferInstance)
  have : IsDominant (Y.fromSpecStalk (genericPoint Y)) := by
    constructor
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← (genericPoint_spec Y).def]
    apply closure_mono
    exact Set.singleton_subset_iff.mpr
      ⟨IsLocalRing.closedPoint Y.functionField, Y.fromSpecStalk_closedPoint⟩
  have hgmem : genericPoint Y ∈ φ.target :=
    ((genericPoint_spec Y).mem_open_set_iff φ.target.isOpen).mpr
      (by simpa using φ.dense_target.nonempty)
  let a := φ.target.fromSpecStalkOfMem (genericPoint Y) hgmem
  have : IsDominant (a ≫ φ.target.ι) := by
    dsimp [a]
    simpa using (inferInstance : IsDominant (Y.fromSpecStalk (genericPoint Y)))
  have : IsDominant a := IsDominant.of_comp_of_isOpenImmersion a φ.target.ι
  have : IsDominant φ.source.ι := Opens.isDominant_ι φ.dense_source
  let g := a ≫ φ.iso.inv ≫ φ.source.ι
  have : IsDominant g := inferInstance
  apply isIso_near_valuation_of_generic_section f y g
  change a ≫ φ.iso.inv ≫ φ.source.ι ≫ f = _
  have hinv : φ.iso.inv ≫ φ.source.ι ≫ f = φ.target.ι := by
    simpa [Scheme.PartialIso.IsOver, Scheme.PartialIso.symm] using hφ.symm
  rw [hinv]
  exact φ.target.fromSpecStalkOfMem_ι _ _

theorem isIso_restrict_iSup
    {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (hU : ∀ i, IsIso (f ∣_ U i)) : IsIso (f ∣_ ⨆ i, U i) := by
  let V : Y.Opens := ⨆ i, U i
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := CategoryTheory.MorphismProperty.isomorphisms Scheme)
    (fun i => V.ι ⁻¹ᵁ U i)
  · apply top_le_iff.mp
    intro z _
    obtain ⟨i, hi⟩ := (show ∃ i, z.1 ∈ U i by
      simpa only [V, TopologicalSpace.Opens.mem_iSup] using z.2)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    rw [(CategoryTheory.MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U i))]
    have heq : V.ι ''ᵁ (V.ι ⁻¹ᵁ U i) = U i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (le_iSup U i)
    rw [heq]
    exact hU i

theorem exists_codim_one_partialIso_of_proper_birational
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [StalkwiseNormal Y] (f : X ⟶ Y) [IsProper f]
    (φ : X.PartialIso Y) (hφ : φ.IsOver f (𝟙 Y)) :
    ∃ ψ : X.PartialIso Y, ψ.IsOver f (𝟙 Y) ∧
      ∀ y : Y, Order.coheight y = 1 → y ∈ ψ.target := by
  classical
  have : IsDominant φ.source.ι := Opens.isDominant_ι φ.dense_source
  let s := φ.iso.inv ≫ φ.source.ι
  have hs : s ≫ f = φ.target.ι := by
    simpa [s, Scheme.PartialIso.IsOver, Scheme.PartialIso.symm] using hφ.symm
  have hφiso : IsIso (f ∣_ φ.target) :=
    isIso_restrict_of_dominant_section f φ.target s hs
  let I := {V : Y.Opens // IsIso (f ∣_ V)}
  let U : Y.Opens := ⨆ V : I, V.1
  have hU : IsIso (f ∣_ U) := isIso_restrict_iSup f _ (fun V => V.2)
  have hT : φ.target ≤ U := le_iSup (fun V : I => V.1) ⟨φ.target, hφiso⟩
  have hS : φ.source ≤ f ⁻¹ᵁ U := by
    intro x hx
    apply hT
    change (φ.source.ι ≫ f) ⟨x, hx⟩ ∈ φ.target
    have heq : φ.iso.hom ≫ φ.target.ι = φ.source.ι ≫ f := by
      simpa [Scheme.PartialIso.IsOver] using hφ
    rw [← heq]
    exact (φ.iso.hom ⟨x, hx⟩).2
  let ψ : X.PartialIso Y := {
    source := f ⁻¹ᵁ U
    dense_source := φ.dense_source.mono hS
    target := U
    dense_target := φ.dense_target.mono hT
    iso := asIso (f ∣_ U) }
  refine ⟨ψ, ?_, ?_⟩
  · change (f ∣_ U) ≫ U.ι ≫ 𝟙 Y = (f ⁻¹ᵁ U).ι ≫ f
    simp
  · intro y hy
    obtain ⟨V, hyV, hV⟩ := isIso_near_codim_one_of_proper_birational f φ hφ y hy
    exact (le_iSup (fun V : I => V.1) ⟨V, hV⟩) hyV
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma dominant_fromSpecStalk {X : Scheme} [IsIntegral X] (x : X) :
    IsDominant (X.fromSpecStalk x) := by
  have hgen : IsDominant (X.fromSpecStalk (genericPoint X)) := by
    constructor
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
    rw [← (genericPoint_spec X)]
    apply closure_mono
    exact Set.singleton_subset_iff.mpr
      ⟨IsLocalRing.closedPoint X.functionField, X.fromSpecStalk_closedPoint⟩
  have heq : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
    X.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have : IsDominant
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        X.fromSpecStalk x) := by
    simpa only [heq] using hgen
  exact IsDominant.of_comp
    (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)))
    (X.fromSpecStalk x)

theorem birational_isIso_stalk_of_quasiFiniteAt
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f]
    (hb : IsBirationalMorphism f) (x : X) (hq : f.QuasiFiniteAt x) :
    IsIso (f.stalkMap x) := by
  classical
  obtain ⟨φ, hφ⟩ := hb
  have hbij : Function.Bijective (dominantFunctionFieldMap f) := by
    refine ⟨(dominantFunctionFieldMap f).injective, ?_⟩
    intro a
    refine ⟨partialIsoFunctionFieldEquiv φ a, ?_⟩
    apply (partialIsoFunctionFieldEquiv φ).injective
    exact partialIso_dominantFunctionFieldMap f φ hφ _
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (Y.presheaf.stalk (f x)) X.functionField :=
    ((dominantFunctionFieldMap f).comp (algebraMap (Y.presheaf.stalk (f x)) Y.functionField)).toAlgebra
  let : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact dominantFunctionFieldMap_algebraMap f x a
  let e : Y.functionField ≃ₐ[Y.presheaf.stalk (f x)] X.functionField :=
    { RingEquiv.ofBijective (dominantFunctionFieldMap f) hbij with commutes' := fun _ => rfl }
  let : IsFractionRing (Y.presheaf.stalk (f x)) X.functionField :=
    IsFractionRing.of_algEquiv e
  let : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  let : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    exact (RingHom.quasiFinite_algebraMap).mp hq
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have he := normal_birational_quasiFinite_local_bijective
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) X.functionField
  exact (ConcreteCategory.isIso_iff_bijective (f.stalkMap x)).mpr he

theorem isIso_near_of_proper_birational_quasiFiniteAt
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (hb : IsBirationalMorphism f) (x : X) (hq : f.QuasiFiniteAt x) :
    ∃ U : Y.Opens, f x ∈ U ∧ IsIso (f ∣_ U) := by
  have : IsIso (f.stalkMap x) := birational_isIso_stalk_of_quasiFiniteAt f hb x hq
  have : IsDominant (X.fromSpecStalk x) := dominant_fromSpecStalk x
  let l := Spec.map (inv (f.stalkMap x)) ≫ X.fromSpecStalk x
  have : IsDominant l := inferInstance
  have hl : l ≫ f = Y.fromSpecStalk (f x) := by
    dsimp [l]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk f]
    simp only [← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id,
      Spec.map_id, Category.id_comp]
  obtain ⟨U, hxU, s, hls, hs⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f l (by simpa using hl)
  have : IsDominant (U.fromSpecStalkOfMem (f x) hxU ≫ s) := by
    rw [← hls]
    infer_instance
  have : IsDominant s := IsDominant.of_comp (U.fromSpecStalkOfMem (f x) hxU) s
  exact ⟨U, hxU, isIso_restrict_of_dominant_section f U s (by simpa using hs)⟩

theorem isIso_of_proper_birational_locallyQuasiFinite
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f] [LocallyQuasiFinite f]
    (hb : IsBirationalMorphism f) : IsIso f := by
  have : Surjective f := inferInstance
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := CategoryTheory.MorphismProperty.isomorphisms Scheme)
  intro y
  obtain ⟨x,rfl⟩ := f.surjective y
  exact isIso_near_of_proper_birational_quasiFiniteAt f hb x (f.quasiFiniteAt x)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma stalk_iso_of_restrict_iso {X Y : Scheme} (f : X ⟶ Y)
    (U : Y.Opens) [IsIso (f ∣_ U)] (x : f ⁻¹ᵁ U) : IsIso (f.stalkMap x.1) := by
  exact (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms CommRingCat)
    (morphismRestrictStalkMap f U x)).mp (by
      change IsIso ((f ∣_ U).stalkMap x)
      exact ((isIso_iff_isIso_stalkMap (f ∣_ U)).mp
        (inferInstance : IsIso (f ∣_ U))).2 x)

theorem exists_unique_prime_over_of_proper_birational
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsProper f] (hf : IsBirationalMorphism f) (p : PrimeDivisor Y) :
    ∃ q : PrimeDivisor X, f q.1 = p.1 ∧ IsIso (f.stalkMap q.1) ∧
      ∀ x : X, f x = p.1 → x = q.1 := by
  obtain ⟨φ,hφ⟩ := hf
  obtain ⟨ψ,hψ,hcodim⟩ := exists_codim_one_partialIso_of_proper_birational f φ hφ
  have : IsDominant ψ.source.ι := Opens.isDominant_ι ψ.dense_source
  have hs : ψ.iso.inv ≫ ψ.source.ι ≫ f = ψ.target.ι := by
    simpa [Scheme.PartialIso.IsOver,Scheme.PartialIso.symm] using hψ.symm
  have : IsIso (f ∣_ ψ.target) := isIso_restrict_of_dominant_section f ψ.target
    (ψ.iso.inv ≫ ψ.source.ι) hs
  obtain ⟨x,hx⟩ := (f ∣_ ψ.target).surjective ⟨p.1,hcodim p.1 p.2⟩
  have hxY : f x.1 = p.1 := by
    simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hx
  have hxc : Order.coheight x.1 = 1 := by
    calc
      _ = Order.coheight x := coheight_eq_of_isOpenImmersion (f ⁻¹ᵁ ψ.target).ι
      _ = Order.coheight ((f ∣_ ψ.target) x) :=
        (coheight_eq_of_isOpenImmersion (f ∣_ ψ.target)).symm
      _ = Order.coheight p.1 := by
        rw [hx]
        exact (coheight_eq_of_isOpenImmersion ψ.target.ι).symm
      _ = 1 := p.2
  refine ⟨⟨x.1,hxc⟩,hxY,stalk_iso_of_restrict_iso f ψ.target x,?_⟩
  intro z hz
  have hzU : z ∈ f ⁻¹ᵁ ψ.target := by
    change f z ∈ ψ.target
    rw [hz]
    exact hcodim p.1 p.2
  have he : (f ∣_ ψ.target) ⟨z,hzU⟩ = (f ∣_ ψ.target) x := by
    apply Subtype.ext
    calc
      _ = f z := morphismRestrict_base_coe f ψ.target ⟨z,hzU⟩
      _ = f x.1 := hz.trans hxY.symm
      _ = _ := (morphismRestrict_base_coe f ψ.target x).symm
  exact congrArg Subtype.val ((f ∣_ ψ.target).isOpenEmbedding.injective he)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma generic_stalk_algebraMap_surjective (Y : Scheme) [IsIntegral Y] :
    Function.Surjective (algebraMap (Y.presheaf.stalk (genericPoint Y)) Y.functionField) := by
  exact Function.surjective_id
lemma birational_generic_fiber {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (hf : IsBirationalMorphism f) (x : X)
    (hx : f x = genericPoint Y) : x = genericPoint X := by
  classical
  obtain ⟨φ,hφ⟩ := hf
  have hbij : Function.Bijective (dominantFunctionFieldMap f) := by
    refine ⟨(dominantFunctionFieldMap f).injective, ?_⟩
    intro a
    refine ⟨partialIsoFunctionFieldEquiv φ a, ?_⟩
    apply (partialIsoFunctionFieldEquiv φ).injective
    exact partialIso_dominantFunctionFieldMap f φ hφ _
  have hy : Function.Surjective (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) := by
    rw [hx]
    intro a
    refine ⟨a,?_⟩
    change Y.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint Y)) a = a
    simp only [TopCat.Presheaf.stalkSpecializes_refl,CommRingCat.id_apply]
  have hs : Function.Surjective (algebraMap (X.presheaf.stalk x) X.functionField) := by
    intro a
    obtain ⟨b,rfl⟩ := hbij.2 a
    obtain ⟨c,rfl⟩ := hy b
    exact ⟨f.stalkMap x c,(dominantFunctionFieldMap_algebraMap f x c).symm⟩
  let e := RingEquiv.ofBijective (algebraMap (X.presheaf.stalk x) X.functionField)
    ⟨IsFractionRing.injective _ _,hs⟩
  have hfield : IsField (X.presheaf.stalk x) := e.toMulEquiv.isField (Field.toIsField _)
  have hz : Order.coheight x = 0 := by
    apply WithBot.coe_injective
    rw [← ringKrullDim_stalk_eq_coheight,ringKrullDim_eq_zero_of_isField hfield]
    rfl
  have hm := Order.coheight_eq_zero.mp hz
  have hsp : x ⤳ genericPoint X := hm (genericPoint_specializes x)
  exact (hsp.antisymm (genericPoint_specializes x)).eq
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOneCurveAux

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def complexProjectiveSpace (N : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ)

noncomputable def projectiveConstants (N : ℕ) :
    ℂ →+* (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ 0) where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C (Fin (N + 1)) a⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

noncomputable def complexProjectiveSpaceMap (N : ℕ) :
    complexProjectiveSpace N ⟶ Spec (.of ℂ) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ) ≫
    Spec.map (CommRingCat.ofHom (projectiveConstants N))

def IsComplexProjective {X : Scheme} (sX : X ⟶ Spec (.of ℂ)) : Prop :=
  ∃ N : ℕ, ∃ i : X ⟶ complexProjectiveSpace N,
    IsClosedImmersion i ∧ i ≫ complexProjectiveSpaceMap N = sX

structure ComplexProjectiveVariety where
  scheme : Scheme
  structureMap : scheme ⟶ Spec (.of ℂ)
  integral : IsIntegral scheme
  connected : ConnectedSpace scheme
  projective : IsComplexProjective structureMap

attribute [instance] ComplexProjectiveVariety.integral ComplexProjectiveVariety.connected

def IsSmoothNfold (X : ComplexProjectiveVariety) (n : ℕ) : Prop :=
  SmoothOfRelativeDimension n X.structureMap

theorem projectiveConstants_bijective (N : ℕ) :
    Function.Bijective (projectiveConstants N) := by
  constructor
  · intro a b hab
    exact MvPolynomial.C_injective (Fin (N + 1)) ℂ (congrArg Subtype.val hab)
  · intro p
    refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
    exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (N + 1))).mpr p.property)).symm

theorem complexProjectiveSpace_isProper (N : ℕ) :
    IsProper (complexProjectiveSpaceMap N) := by
  let A := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ
  let : IsScalarTower ℂ (A 0) (MvPolynomial (Fin (N + 1)) ℂ) :=
    IsScalarTower.of_algebraMap_eq (R := ℂ) (S := A 0) (A := MvPolynomial (Fin (N + 1)) ℂ) fun _ => rfl
  let : Algebra.FiniteType (A 0) (MvPolynomial (Fin (N + 1)) ℂ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (A 0)
      (MvPolynomial (Fin (N + 1)) ℂ)
  let e := RingEquiv.ofBijective (projectiveConstants N) (projectiveConstants_bijective N)
  let : IsIso (CommRingCat.ofHom (projectiveConstants N)) := by
    exact e.toCommRingCatIso.isIso_hom
  have hp : IsProper (Proj.toSpecZero A) := inferInstance
  have he : IsIso (Spec.map (CommRingCat.ofHom (projectiveConstants N))) := inferInstance
  let := hp
  let := he
  change IsProper (Proj.toSpecZero A ≫
    Spec.map (CommRingCat.ofHom (projectiveConstants N)))
  let ht : IsProper (Spec.map (CommRingCat.ofHom (projectiveConstants N))) := inferInstance
  exact IsProper.comp_iff.mpr hp

theorem isProper_of_isComplexProjective {X : Scheme} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsComplexProjective sX) : IsProper sX := by
  obtain ⟨N, i, hi, rfl⟩ := hX
  let := hi
  let := complexProjectiveSpace_isProper N
  infer_instance

end NumericalDimensionOneCurveAux

end OAI
