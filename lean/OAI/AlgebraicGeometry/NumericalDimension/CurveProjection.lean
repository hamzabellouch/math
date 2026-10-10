import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.FiniteCurveMaps
import OAI.AlgebraicGeometry.NumericalDimension.SurfaceIntersection

namespace OAI

/-! Curve Projection. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X C Y : Scheme} [IsIntegral X] [IsIntegral C] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian C] [IsLocallyNoetherian Y]
  [StalkwiseNormal Y] [CompactSpace X] [CompactSpace C]
  (sX : X ⟶ Spec (.of ℂ)) (sC : C ⟶ Spec (.of ℂ))
  [SmoothOfRelativeDimension 1 sX] [SmoothOfRelativeDimension 1 sC]
  [IsProper sX] [IsProper sC]
include sX sC in

theorem properCurveDegree_comp_finite (f : X ⟶ C) [IsFinite f] [IsDominant f]
    (i : C ⟶ Y) (D : cartierDivisors (X := Y)) :
    properCurveDegree (f ≫ i) D =
      (curveFieldDegree f : ℤ) * properCurveDegree i D := by
  let : Smooth sX := SmoothOfRelativeDimension.smooth 1 sX
  let : Smooth sC := SmoothOfRelativeDimension.smooth 1 sC
  let : StalkwiseNormal X := ⟨integrallyClosed_stalk_of_smooth_field sX⟩
  let : StalkwiseNormal C := ⟨integrallyClosed_stalk_of_smooth_field sC⟩
  obtain ⟨E,hE⟩ := exists_pulledCartierRepresentative i D.1 D.2
  obtain ⟨F,hF⟩ := exists_cartierPullback f E hE.isCartier
  rw [properCurveDegree_eq sX (f ≫ i) D F (hE.comp_dominant f i hF),
    properCurveDegree_eq sC i D E hE]
  exact smoothCurve_degree_cartierPullback sX sC f hF
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem curveFieldDegree_pos {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] : 0 < curveFieldDegree f := by
  obtain ⟨V,hV,hη,_⟩ := exists_isAffineOpen_mem_and_subset
    (show f (genericPoint X) ∈ (⊤ : Y.Opens) from trivial)
  let : Nonempty V := ⟨⟨f (genericPoint X),hη⟩⟩
  let : Nonempty (f ⁻¹ᵁ V) := ⟨⟨genericPoint X,hη⟩⟩
  let hU := hV.preimage f
  let := (f.app V).hom.toAlgebra
  let : Module.Finite Γ(Y,V) Γ(X,f ⁻¹ᵁ V) := f.finite_app V hV
  let : IsSchemeTheoreticallyDominant f := .of_isDominant f
  let : Module.IsTorsionFree Γ(Y,V) Γ(X,f ⁻¹ᵁ V) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (f.app_injective V)
  rw [curveFieldDegree_eq_affine f V hV hU]
  exact Module.finrank_pos
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma dominantFunctionFieldMap_spec {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    Spec.map (CommRingCat.ofHom (dominantFunctionFieldMap f)) ≫
      Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ f := by
  change Spec.map ((Y.presheaf.stalkCongr
    (Inseparable.of_eq (dominant_genericPoint f).symm)).hom ≫
      f.stalkMap (genericPoint X)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (f.stalkMap (genericPoint X)) ≫
    Spec.map (Y.presheaf.stalkSpecializes
      (Inseparable.of_eq (dominant_genericPoint f)).specializes) ≫
        Y.fromSpecStalk (genericPoint Y) = _
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u

theorem valuationRing_stalk_of_smooth_curve
    {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 sC] (x : C) :
    ValuationRing (C.presheaf.stalk x) := by
  let : Smooth sC := SmoothOfRelativeDimension.smooth 1 sC
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  let : IsIntegrallyClosed (C.presheaf.stalk x) :=
    integrallyClosed_stalk_of_smooth_field sC x
  let : Ring.KrullDimLE 1 (C.presheaf.stalk x) :=
    krullDimLE_of_coheight_le (coheight_le_of_smooth_dimension sC 1 x)
  by_cases hfield : IsField (C.presheaf.stalk x)
  · let := hfield.toField
    infer_instance
  · let : Ring.DimensionLEOne (C.presheaf.stalk x) :=
      ⟨fun {I} hI hprime =>
        Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance I hI hprime⟩
    let : IsDedekindDomain (C.presheaf.stalk x) := { }
    let : IsDiscreteValuationRing (C.presheaf.stalk x) :=
      ((IsDiscreteValuationRing.TFAE (C.presheaf.stalk x) hfield).out 3 1).mp
        (show IsDedekindDomain (C.presheaf.stalk x) from inferInstance)
    infer_instance

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme
universe u

lemma partial_fromFunctionField_eq {C Y : Scheme.{u}} [IsIntegral C]
    (f : C.PartialMap Y) {x : C} (hx : x ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
        f.fromSpecStalkOfMem hx := by
  have hη : genericPoint C ∈ f.domain :=
    (genericPoint_specializes x).mem_open f.domain.2 hx
  have h : f.domain.fromSpecStalkOfMem (genericPoint C) hη =
      Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
        f.domain.fromSpecStalkOfMem x hx := by
    apply (cancel_mono f.domain.ι).mp
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (C.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm
  change f.domain.fromSpecStalkOfMem (genericPoint C) hη ≫ f.hom = _
  rw [h, Category.assoc]
  rfl

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme
universe u

theorem exists_extension_from_functionField_of_smooth_curve
    {k : Type u} [Field k] {C Y : Scheme.{u}} [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 sC]
    (sY : Y ⟶ Spec (.of k)) [IsProper sY]
    (g : Spec C.functionField ⟶ Y)
    (hg : g ≫ sY = C.fromSpecStalk (genericPoint C) ≫ sC) :
    ∃ f : C ⟶ Y, C.fromSpecStalk (genericPoint C) ≫ f = g ∧ f ≫ sY = sC := by
  let : Y.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from sY]
    infer_instance
  let r := RationalMap.ofFunctionField sC sY g hg
  have hr : r.fromFunctionField = g := RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have hdomain : r.domain = ⊤ := by
    apply top_unique
    intro x _
    let : ValuationRing (C.presheaf.stalk x) := valuationRing_stalk_of_smooth_curve sC x
    have hv : ValuativeCriterion.Existence sY := by
      have h : UniversallyClosed sY := inferInstance
      rw [UniversallyClosed.eq_valuativeCriterion] at h
      exact h.1
    have hw : g ≫ sY =
        Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
          (C.fromSpecStalk x ≫ sC) := by
      rw [hg, ← Category.assoc]
      exact congrArg (fun t => t ≫ sC)
        (C.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm
    obtain ⟨l, hlg, hl⟩ := (hv {
      R := C.presheaf.stalk x
      commRing := inferInstanceAs (CommRing (C.presheaf.stalk x))
      domain := inferInstanceAs (IsDomain (C.presheaf.stalk x))
      K := C.functionField
      i₁ := g
      i₂ := C.fromSpecStalk x ≫ sC
      commSq := ⟨hw⟩ }).exists_lift
    let p := PartialMap.ofFromSpecStalk sC sY l hl
    have hx : x ∈ p.domain := PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
    apply RationalMap.mem_domain.mpr
    refine ⟨p, hx, RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
    rw [RationalMap.fromFunctionField_toRationalMap, partial_fromFunctionField_eq p hx,
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk, hr]
    exact hlg
  let p := r.toPartialMap
  have hpdom : p.domain = ⊤ := hdomain
  let : IsIso p.domain.ι := by
    rw [hpdom]
    change IsIso C.topIso.hom
    infer_instance
  let f := inv p.domain.ι ≫ p.hom
  have hf : C.fromSpecStalk (genericPoint C) ≫ f = g := by
    have hη : genericPoint C ∈ p.domain := by rw [hpdom]; trivial
    have hi : C.fromSpecStalk (genericPoint C) ≫ inv p.domain.ι =
        p.domain.fromSpecStalkOfMem (genericPoint C) hη := by
      apply (cancel_mono p.domain.ι).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    change C.fromSpecStalk (genericPoint C) ≫ inv p.domain.ι ≫ p.hom = g
    rw [← Category.assoc, hi]
    change p.fromFunctionField = g
    rw [← RationalMap.fromFunctionField_toRationalMap, RationalMap.toRationalMap_toPartialMap, hr]
  refine ⟨f, hf, ?_⟩
  let : IsDominant (C.fromSpecStalk (genericPoint C)) := ⟨by
    have hden : Dense ({genericPoint C} : Set C) :=
      dense_iff_closure_eq.mpr (genericPoint_spec C)
    exact hden.mono (Set.singleton_subset_iff.mpr ⟨_, C.fromSpecStalk_closedPoint⟩)⟩
  apply ext_of_isDominant (C.fromSpecStalk (genericPoint C))
  rw [← Category.assoc, hf, hg]

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem curve_lift_through_proper_functionField_iso
    {C T N : Scheme} [IsIntegral C] [IsIntegral T] [IsIntegral N]
    [NoetherianSpace C] [Nontrivial T]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]
    (sT : T ⟶ Spec (.of ℂ)) [IsProper sT]
    (ν : N ⟶ T) [IsProper ν] [IsDominant ν]
    (hν : Function.Bijective (dominantFunctionFieldMap ν))
    (g : C ⟶ T) [IsDominant g] (hg : g ≫ sT = sC) :
    ∃ τ : C ⟶ N, τ ≫ ν = g ∧ IsFinite τ ∧ IsDominant τ := by
  let e := RingEquiv.ofBijective (dominantFunctionFieldMap ν) hν
  let a : N.functionField →+* C.functionField :=
    (dominantFunctionFieldMap g).comp e.symm.toRingHom
  have ha : a.comp (dominantFunctionFieldMap ν) = dominantFunctionFieldMap g := by
    ext r
    exact congrArg (dominantFunctionFieldMap g) (e.symm_apply_apply r)
  let G : Spec C.functionField ⟶ N :=
    Spec.map (CommRingCat.ofHom a) ≫ N.fromSpecStalk (genericPoint N)
  have hG : G ≫ ν = C.fromSpecStalk (genericPoint C) ≫ g := by
    dsimp only [G]
    rw [Category.assoc, ← dominantFunctionFieldMap_spec ν, ← Category.assoc]
    erw [← Spec.map_comp, ← dominantFunctionFieldMap_spec g]
    congr 2
    exact CommRingCat.hom_ext ha
  have hGovern : G ≫ (ν ≫ sT) = C.fromSpecStalk (genericPoint C) ≫ sC := by
    rw [← Category.assoc, hG, Category.assoc, hg]
  obtain ⟨τ,hτ,hτover⟩ :=
    exists_extension_from_functionField_of_smooth_curve sC (ν ≫ sT) G hGovern
  have heq : τ ≫ ν = g := by
    apply ext_of_isDominant_of_isSeparated sT
      (by simpa only [Category.assoc, hg] using hτover)
      (C.fromSpecStalk (genericPoint C))
    rw [← Category.assoc, hτ, hG]
  have : IsDominant (Spec.map (CommRingCat.ofHom a)) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    exact ((RingHom.injective_iff_ker_eq_bot a).mp a.injective).le.trans bot_le
  have : IsDominant G := inferInstance
  have : IsDominant (C.fromSpecStalk (genericPoint C) ≫ τ) := by
    rw [hτ]
    infer_instance
  have : IsDominant τ := IsDominant.of_comp (C.fromSpecStalk (genericPoint C)) τ
  have : IsProper (τ ≫ (ν ≫ sT)) := by
    rw [hτover]
    infer_instance
  have : IsProper τ := IsProper.of_comp τ (ν ≫ sT)
  have : Surjective ν := inferInstance
  let : Nontrivial N := ν.surjective.nontrivial
  exact ⟨τ,heq,finite_of_proper_dominant_from_smooth_curve sC τ,inferInstance⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma reduced_ker_radical {X Y : Scheme} [IsReduced X] (f : X ⟶ Y) [QuasiCompact f] :
    f.ker.radical = f.ker := by
  apply le_antisymm
  · intro U a ha
    rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply] at ha
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    obtain ⟨n,hn⟩ := ha
    exact IsNilpotent.eq_zero ⟨n, by simpa only [RingHom.mem_ker, map_pow] using hn⟩
  · exact Scheme.IdealSheafData.le_radical _

theorem exists_lift_closed_of_reduced {X Y Z : Scheme} [IsReduced X]
    (f : X ⟶ Y) [QuasiCompact f] (i : Z ⟶ Y) [IsClosedImmersion i]
    (h : Set.range f ⊆ Set.range i) : ∃ g : X ⟶ Z, g ≫ i = f := by
  have hs : f.ker.support ≤ i.ker.support := by
    change (f.ker.support : Set Y) ⊆ i.ker.support
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
    exact closure_mono h
  have hk : i.ker ≤ f.ker := by
    rw [← reduced_ker_radical f, ← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hs
  exact ⟨IsClosedImmersion.lift i f hk, IsClosedImmersion.lift_fac i f hk⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem factor_dominant_pointClosure {C X : Scheme} [IsIntegral C]
    (g : C ⟶ X) [QuasiCompact g] :
    ∃ h : C ⟶ pointClosure (g (genericPoint C)),
      h ≫ pointClosureι (g (genericPoint C)) = g ∧ IsDominant h := by
  let p := g (genericPoint C)
  have hr : Set.range g ⊆ Set.range (pointClosureι p) := by
    rw [pointClosure_range]
    rintro x ⟨y,rfl⟩
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes y).map g.continuous)
  obtain ⟨h,hh⟩ := exists_lift_closed_of_reduced g (pointClosureι p) hr
  refine ⟨h,hh,⟨?_⟩⟩
  rw [denseRange_iff_closure_range,
    (pointClosureι p).isEmbedding.closure_eq_preimage_closure_image]
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hh]
  have hc : closure (Set.range g) = closure ({p} : Set X) := by
    simpa only [Set.image_univ] using ((genericPoint_spec C).image g.continuous).symm
  rw [hc, ← pointClosure_range]
  exact Set.eq_univ_of_forall (fun x => ⟨x,rfl⟩)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem curve_factors_through_normalized_image
    {C X : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (g : C ⟶ X) (hg : g ≫ sX = sC)
    (hnc : ¬ IsClosed ({g (genericPoint C)} : Set X)) :
    let T := pointClosure (g (genericPoint C))
    let ν := (T.fromSpecStalk (genericPoint T)).fromNormalization
    ∃ τ : C ⟶ (T.fromSpecStalk (genericPoint T)).normalization,
      τ ≫ ν ≫ pointClosureι (g (genericPoint C)) = g ∧ IsFinite τ ∧ IsDominant τ := by
  let T := pointClosure (g (genericPoint C))
  let i := pointClosureι (g (genericPoint C))
  let n := T.fromSpecStalk (genericPoint T)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have : AlgebraicGeometry.IsNoetherian C := ⟨⟩
  have : IsProper (g ≫ sX) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g sX
  have : Nontrivial T := pointClosure_nontrivial _ hnc
  have : IsProper (i ≫ sX) := inferInstance
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (i ≫ sX)
  have : AlgebraicGeometry.IsNoetherian T := ⟨⟩
  have : IsFinite n.fromNormalization := finite_genericNormalization (i ≫ sX)
  obtain ⟨h,hh,hdom⟩ := factor_dominant_pointClosure g
  have hhov : h ≫ (i ≫ sX) = sC := by rw [← Category.assoc, hh, hg]
  obtain ⟨τ,hτ,hfin,hτdom⟩ := curve_lift_through_proper_functionField_iso sC
    (i ≫ sX) n.fromNormalization genericNormalization_bijective_functionField h hhov
  exact ⟨τ, by rw [← Category.assoc, hτ, hh],hfin,hτdom⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem surface_curve_degree_projection
    {C X : Scheme} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X] [StalkwiseNormal X] [CompactSpace C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]
    (sX : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 2 sX] [IsProper sX]
    (g : C ⟶ X) (hg : g ≫ sX = sC)
    (hp : Order.coheight (g (genericPoint C)) = 1) :
    ∃ d : ℕ, 0 < d ∧ ∀ D : cartierDivisors (X := X),
      properCurveDegree g D = (d : ℤ) * surfaceCartierPrimeDegree sX D ⟨_,hp⟩ := by
  let p : PrimeDivisor X := ⟨_,hp⟩
  let T := pointClosure p.1
  let n := T.fromSpecStalk (genericPoint T)
  let i := n.fromNormalization ≫ pointClosureι p.1
  have hnc : ¬ IsClosed ({p.1} : Set X) := by
    intro h
    have he := coheight_eq_of_smooth_closed sX 2 p.1 h
    rw [p.2] at he
    norm_num at he
  obtain ⟨τ,hτ,hfin,hdom⟩ := curve_factors_through_normalized_image sC sX g hg hnc
  have : SmoothOfRelativeDimension 1 (i ≫ sX) := by
    simpa only [i,Category.assoc] using surface_prime_normalization_smooth sX p.1 p.2
  have : IsProper (i ≫ sX) := by
    simpa only [i,Category.assoc] using surface_prime_normalization_proper sX p.1
  have : IsLocallyNoetherian n.normalization := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have : CompactSpace n.normalization := QuasiCompact.compactSpace_of_compactSpace (i ≫ sX)
  refine ⟨curveFieldDegree τ,curveFieldDegree_pos τ,?_⟩
  intro D
  change properCurveDegree g D = (curveFieldDegree τ : ℤ) * properCurveDegree i D
  rw [← properCurveDegree_comp_finite sC (i ≫ sX) τ i D]
  exact congrArg (fun t => properCurveDegree t D) hτ.symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem pointClosure_map_functionField_bijective
    {X Y : Scheme} (f : X ⟶ Y) [IsProper f] (q : X) [IsIso (f.stalkMap q)] :
    ∃ r : pointClosure q ⟶ pointClosure (f q),
      r ≫ pointClosureι (f q) = pointClosureι q ≫ f ∧ IsProper r ∧
      ∃ (_ : IsDominant r), Function.Bijective (dominantFunctionFieldMap r) := by
  have : IsIso (f.residueFieldMap q) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  have he : (pointClosureι q ≫ f) (genericPoint (pointClosure q)) = f q := by
    rw [Scheme.Hom.comp_apply, pointClosure_generic]
  have hv := factor_dominant_pointClosure (pointClosureι q ≫ f)
  rw [he] at hv
  obtain ⟨r,hr,hdom⟩ := hv
  have : IsProper (r ≫ pointClosureι (f q)) := by rw [hr]; infer_instance
  have : IsProper r := IsProper.of_comp r (pointClosureι (f q))
  refine ⟨r,hr,inferInstance,hdom,?_⟩
  let a : Spec (X.residueField q) ⟶ pointClosure q := (X.fromSpecResidueField q).toImage
  let b : Spec (Y.residueField (f q)) ⟶ pointClosure (f q) :=
    (Y.fromSpecResidueField (f q)).toImage
  have ha : a ≫ pointClosureι q = X.fromSpecResidueField q :=
    Scheme.Hom.toImage_imageι _
  have hb : b ≫ pointClosureι (f q) = Y.fromSpecResidueField (f q) :=
    Scheme.Hom.toImage_imageι _
  have : IsDominant a := inferInstanceAs (IsDominant (X.fromSpecResidueField q).toImage)
  have : IsPreimmersion a := by
    have : IsPreimmersion (a ≫ pointClosureι q) := by rw [ha]; infer_instance
    exact IsPreimmersion.of_comp a (pointClosureι q)
  have : IsPreimmersion b := by
    have : IsPreimmersion (b ≫ pointClosureι (f q)) := by rw [hb]; infer_instance
    exact IsPreimmersion.of_comp b (pointClosureι (f q))
  have hd : a ≫ r = Spec.map (f.residueFieldMap q) ≫ b := by
    apply (cancel_mono (pointClosureι (f q))).mp
    rw [Category.assoc,hr,← Category.assoc,ha,Category.assoc,hb,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have : IsPreimmersion (a ≫ r) := by rw [hd]; infer_instance
  have hsur := (dominantFunctionFieldMap_bijective_of_preimmersion (a ≫ r)).2
  refine ⟨(dominantFunctionFieldMap r).injective,?_⟩
  intro z
  obtain ⟨w,hw⟩ := hsur (dominantFunctionFieldMap a z)
  refine ⟨w,(dominantFunctionFieldMap a).injective ?_⟩
  simpa only [dominantFunctionFieldMap_comp_apply] using hw
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma curveFieldDegree_eq_one {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (dominantFunctionFieldMap f)) : curveFieldDegree f = 1 := by
  let := (dominantFunctionFieldMap f).toAlgebra
  exact Module.finrank_of_bijective_algebraMap hf
lemma dominantFunctionFieldMap_bijective_comp {X Y Z : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g]
    (hf : Function.Bijective (dominantFunctionFieldMap f))
    (hg : Function.Bijective (dominantFunctionFieldMap g)) :
    Function.Bijective (dominantFunctionFieldMap (f ≫ g)) := by
  have he : (dominantFunctionFieldMap (f ≫ g) : Z.functionField → X.functionField) =
      (dominantFunctionFieldMap f) ∘ (dominantFunctionFieldMap g) :=
    funext (dominantFunctionFieldMap_comp_apply f g)
  rw [he]
  exact hf.comp hg
lemma dominantFunctionFieldMap_bijective_of_comp {X Y Z : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g]
    (hfg : Function.Bijective (dominantFunctionFieldMap (f ≫ g))) :
    Function.Bijective (dominantFunctionFieldMap f) := by
  refine ⟨(dominantFunctionFieldMap f).injective,?_⟩
  intro x
  obtain ⟨z,hz⟩ := hfg.2 x
  exact ⟨dominantFunctionFieldMap g z, by
    simpa only [dominantFunctionFieldMap_comp_apply] using hz⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma IsCartierPullback.order_eq_of_equation
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal Y]
    {f : X ⟶ Y} [IsDominant f] {D : WeilDivisor Y} {P : WeilDivisor X}
    (hP : IsCartierPullback f D P) {U : Y.Opens} {a : Y.functionField}
    (ha : a ≠ 0) (hDa : ∀ q : PrimeDivisor Y, q.1 ∈ U → D q = Y.ord a q.1)
    (p : PrimeDivisor X) (hpU : f p.1 ∈ U) :
    P p = X.ord (dominantFunctionFieldMap f a) p.1 := by
  obtain ⟨V, _, hpV, b, hb, hDb, hPb⟩ := hP p.1
  rw [hPb p hpV]
  exact pulled_equation_order_eq f hb ha hDb hDa p hpV hpU

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {C X Y : Scheme} [IsIntegral C] [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian C] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [StalkwiseNormal Y]

theorem IsPulledCartierRepresentative.of_cartierPullback
    (g : C ⟶ X) (f : X ⟶ Y) [IsDominant f]
    {D : WeilDivisor Y} {P : WeilDivisor X} {E : WeilDivisor C}
    (hP : IsCartierPullback f D P)
    (hE : IsPulledCartierRepresentative (g ≫ f) D E) :
    IsPulledCartierRepresentative g P E := by
  obtain ⟨U,_hU,hηU,a,ha,hDa,hE⟩ := hE
  obtain ⟨V,hV,hηV,hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show g (genericPoint C) ∈ f ⁻¹ᵁ U from hηU)
  refine ⟨V,hV,hηV,dominantFunctionFieldMap f a,(map_ne_zero _).mpr ha,?_,?_⟩
  · exact fun p hp => hP.order_eq_of_equation ha hDa p (hVU hp)
  intro x
  obtain ⟨U',_hU',hxU,b,hb,hDb,u,hu,heu,hEu⟩ := hE x
  obtain ⟨V',hV',hxV,hV'U⟩ := exists_isAffineOpen_mem_and_subset
    (show g x ∈ f ⁻¹ᵁ U' from hxU)
  refine ⟨V',hV',hxV,dominantFunctionFieldMap f b,(map_ne_zero _).mpr hb,
    (fun p hp => hP.order_eq_of_equation hb hDb p (hV'U hp)),
    f.stalkMap (g (genericPoint C)) u,hu.map _,?_,?_⟩
  · calc
      _ = dominantFunctionFieldMap f
          (algebraMap (Y.presheaf.stalk ((g ≫ f) (genericPoint C))) Y.functionField u) :=
        (dominantFunctionFieldMap_algebraMap f (g (genericPoint C)) u).symm
      _ = _ := by rw [heu,map_div₀]
  · intro p hp
    rw [hEu p (hV'U hp),Scheme.Hom.stalkMap_comp]
    rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {C X Y : Scheme} [IsIntegral C] [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian C] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [StalkwiseNormal X] [StalkwiseNormal Y] [CompactSpace C]
  (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]
include sC in

theorem properCurveDegree_ambientPullback (g : C ⟶ X) (f : X ⟶ Y) [IsDominant f]
    (D : cartierDivisors (X := Y)) (P : WeilDivisor X) (hP : IsCartierPullback f D.1 P) :
    properCurveDegree g ⟨P,hP.isCartier⟩ = properCurveDegree (g ≫ f) D := by
  obtain ⟨E,hE⟩ := exists_pulledCartierRepresentative (g ≫ f) D.1 D.2
  rw [properCurveDegree_eq sC (g ≫ f) D E hE,
    properCurveDegree_eq sC g ⟨P,hP.isCartier⟩ E (hE.of_cartierPullback g f hP)]
end NumericalDimensionOne

end OAI
