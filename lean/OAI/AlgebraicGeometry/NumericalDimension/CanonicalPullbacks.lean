import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.TerminalModels

namespace OAI

/-! Canonical Pullbacks. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma rationalTopFormPullback_birational_bijective
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (f : X ⟶ Y) [IsDominant f] (hb : IsBirationalMorphism f)
    (hf : f ≫ sY = sX) (n : ℕ) :
    Function.Bijective (rationalTopFormPullback (.of ℂ) sX sY f hf n) := by
  let := schemeFieldAlgebra (.of ℂ) sX
  let := schemeFieldAlgebra (.of ℂ) sY
  let := (dominantFunctionFieldMap f).toAlgebra
  let : IsScalarTower ℂ Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar (.of ℂ) sX sY f hf a).symm)
  apply topDifferentialMap_bijective_of_algebraMap_bijective ℂ Y.functionField X.functionField
  obtain ⟨φ,hφ⟩ := hb
  refine ⟨(dominantFunctionFieldMap f).injective, ?_⟩
  intro a
  refine ⟨partialIsoFunctionFieldEquiv φ a, ?_⟩
  apply (partialIsoFunctionFieldEquiv φ).injective
  exact partialIso_dominantFunctionFieldMap f φ hφ _
lemma exists_canonicalDivisorOf_nonzero
    (W : ComplexProjectiveVariety) (n : ℕ) (hW : IsSmoothNfold W n)
    (ω : rationalTopForms (.of ℂ) W.structureMap n) (hω : ω ≠ 0) :
    ∃ KW : WeilDivisor W.scheme, IsCanonicalDivisorOf (.of ℂ) W.structureMap n ω KW := by
  let : SmoothOfRelativeDimension n W.structureMap := hW
  obtain ⟨D,η,hD⟩ := exists_canonicalDivisor_of_smooth W.structureMap n
  let := schemeFieldAlgebra (.of ℂ) W.structureMap
  obtain ⟨b⟩ := nonempty_smooth_canonical_field_basis W.structureMap n
  let a := b.repr η 0
  let a' := b.repr ω 0
  have hη : η = a • b 0 := basis_singleton_repr b η
  have hω' : ω = a' • b 0 := basis_singleton_repr b ω
  have ha : a ≠ 0 := by
    intro ha
    exact hD.1 (by simpa [ha] using hη)
  have ha' : a' ≠ 0 := by
    intro ha'
    exact hω (by simpa [ha'] using hω')
  have heq : (a' / a) • η = ω := by
    rw [hη,← mul_smul,div_mul_cancel₀ _ ha,← hω']
  refine ⟨D + principalWeilDivisor (a' / a),?_⟩
  simpa only [heq] using canonicalDivisorOf_smul W.structureMap n hD (div_ne_zero ha' ha)
lemma exists_canonicalDivisorOf_birational_pullback {n : ℕ}
    (Y : CanonicalModel n) (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    (q : W.scheme ⟶ Y.scheme) [IsDominant q] (hqb : IsBirationalMorphism q)
    (hq : q ≫ Y.structureMap = W.structureMap) :
    ∃ KW : WeilDivisor W.scheme, IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap q hq n Y.form) KW := by
  apply exists_canonicalDivisorOf_nonzero W n hW
  intro hz
  apply Y.canonical_of_form.1
  have hi := (rationalTopFormPullback_birational_bijective W.structureMap Y.structureMap
    q hqb hq n).1
  apply hi
  exact hz.trans (by simp only [rationalTopFormPullback,map_zero])
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma CompatibleCanonicalData.iff_morphism {n : ℕ} {X Y : CanonicalModel n}
    (f : X.scheme ⟶ Y.scheme) [hfDom : IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (φ : X.scheme.PartialIso Y.scheme) (hφ : φ.IsOver f (𝟙 Y.scheme))
    (hbase : φ.IsOver X.structureMap Y.structureMap) :
    CompatibleCanonicalData X Y φ hbase ↔ X.form =
      rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n Y.form := by
  have hb : IsBirationalMorphism φ.source.ι :=
    φ.source.ι.birationalOver (𝟙 X.scheme) φ.source.ι (Category.comp_id _)
  have hi := (rationalTopFormPullback_birational_bijective
    (φ.source.ι ≫ X.structureMap) X.structureMap φ.source.ι hb rfl n).1
  have he : φ.source.ι ≫ f = φ.iso.hom ≫ φ.target.ι := by
    simpa only [Scheme.PartialIso.IsOver,Category.comp_id] using (show φ.iso.hom ≫ φ.target.ι ≫ (𝟙 Y.scheme) = φ.source.ι ≫ f from hφ).symm
  have hcomp : (φ.source.ι ≫ f) ≫ Y.structureMap = φ.source.ι ≫ X.structureMap := by
    rw [Category.assoc,hf]
  have hiso : (φ.iso.hom ≫ φ.target.ι) ≫ Y.structureMap = φ.source.ι ≫ X.structureMap := by
    simpa only [Category.assoc] using hbase
  have heq := congrFun (rationalTopFormPullback_congr (.of ℂ)
    (φ.source.ι ≫ X.structureMap) Y.structureMap (φ.source.ι ≫ f)
    (φ.iso.hom ≫ φ.target.ι) hcomp hiso he n) Y.form
  have hw := rationalTopFormPullback_comp (.of ℂ)
    (φ.source.ι ≫ X.structureMap) X.structureMap Y.structureMap
    φ.source.ι f rfl hf n Y.form
  change rationalTopFormPullback _ _ _ φ.source.ι rfl n X.form =
    rationalTopFormPullback _ _ _ (φ.iso.hom ≫ φ.target.ι) hiso n Y.form ↔ _
  rw [← heq,hw]
  exact hi.eq_iff
noncomputable def canonicalModelOfForm (W : ComplexProjectiveVariety) (n : ℕ)
    (hW : IsSmoothNfold W n) (ω : rationalTopForms (.of ℂ) W.structureMap n)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n ω KW) : CanonicalModel n := by
  let : SmoothOfRelativeDimension n W.structureMap := hW
  have hCartier : IsCartierDivisor KW :=
    isCartier_of_isCanonical W.structureMap n ⟨_,hKW⟩
  exact {
    toNormalProjectiveVariety := { toComplexProjectiveVariety := W, normal := smoothNormal W hW }
    form := ω
    canonical := KW
    canonical_of_form := hKW
    qCartier := ⟨1,by decide,KW,hCartier,by simp⟩ }
lemma exists_common_canonicalDivisor {n : ℕ}
    (X Y : CanonicalModel n) (φ : X.scheme.PartialIso Y.scheme)
    (hbase : φ.IsOver X.structureMap Y.structureMap)
    (hc : CompatibleCanonicalData X Y φ hbase)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q]
    (hp : p ≫ X.structureMap = W.structureMap) (hq : q ≫ Y.structureMap = W.structureMap)
    (θ : W.scheme.PartialIso X.scheme) (hθp : θ.IsOver p (𝟙 X.scheme))
    (hθq : (θ.trans φ).IsOver q (𝟙 Y.scheme)) :
    ∃ KW : WeilDivisor W.scheme,
      IsCanonicalDivisorOf (.of ℂ) W.structureMap n
        (rationalTopFormPullback (.of ℂ) W.structureMap X.structureMap p hp n X.form) KW ∧
      IsCanonicalDivisorOf (.of ℂ) W.structureMap n
        (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap q hq n Y.form) KW := by
  obtain ⟨KW,hKW⟩ := exists_canonicalDivisorOf_birational_pullback X W hW p ⟨θ,hθp⟩ hp
  let Z := canonicalModelOfForm W n hW _ KW hKW
  have hθbase : θ.IsOver Z.structureMap X.structureMap := by
    change θ.iso.hom ≫ θ.target.ι ≫ X.structureMap = θ.source.ι ≫ W.structureMap
    rw [← hp,← Category.assoc,← Category.assoc]
    exact congrArg (fun r => r ≫ X.structureMap)
      (show θ.iso.hom ≫ θ.target.ι = θ.source.ι ≫ p from by
        simpa only [Scheme.PartialIso.IsOver,Category.comp_id] using hθp)
  have hZX : CompatibleCanonicalData Z X θ hθbase :=
    (CompatibleCanonicalData.iff_morphism (X := Z) (Y := X) p (hfDom := inferInstanceAs (IsDominant p)) hp θ hθp hθbase).mpr rfl
  have hZY := hZX.trans hc
  have hform := (CompatibleCanonicalData.iff_morphism (X := Z) (Y := Y) q (hfDom := inferInstanceAs (IsDominant q)) hq (θ.trans φ) hθq
    (hθbase.trans hbase)).mp hZY
  refine ⟨KW,hKW,?_⟩
  change rationalTopFormPullback (.of ℂ) W.structureMap X.structureMap p hp n X.form =
    rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap q hq n Y.form at hform
  rw [← hform]
  exact hKW
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma exists_qCartierPullback
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [StalkwiseNormal Y] [CompactSpace X]
    (f : X ⟶ Y) [IsDominant f] (D : QWeilDivisor Y) (hD : IsQCartierDivisor D) :
    ∃ E : QWeilDivisor X, IsQCartierPullback f D E := by
  obtain ⟨m,hm,A,hA,hAD⟩ := hD
  obtain ⟨B,hB⟩ := exists_cartierPullback f A hA
  let E : QWeilDivisor X := (m : ℚ)⁻¹ • rationalWeilDivisor B
  refine ⟨E,m,hm,A,B,hA,hAD,?_,hB⟩
  ext p
  change (m : ℚ) * ((m : ℚ)⁻¹ * (B p : ℚ)) = (B p : ℚ)
  rw [← mul_assoc,mul_inv_cancel₀ (show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne'),one_mul]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma restricted_partialIso_map {X Y : Scheme} (φ : X.PartialIso Y)
    (V : X.Opens) (hV : Dense (V : Set X)) (hle : V ≤ φ.source) :
    (φ.restrictSource V hV hle).iso.hom ≫ (φ.restrictSource V hV hle).target.ι =
      X.homOfLE hle ≫ φ.iso.hom ≫ φ.target.ι := by
  have h : (Scheme.Opens.isoOfLE hle).inv ≫ (φ.source.ι ⁻¹ᵁ V).ι = X.homOfLE hle := by
    apply (cancel_mono φ.source.ι).mp
    simp only [Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  simp [Scheme.PartialIso.restrictSource]
  rw [← Category.assoc,h]
lemma common_model_on_partial_locus
    {W X Y : Scheme} [IsIntegral W] [X.IsSeparated]
    (p : W ⟶ X) (q : W ⟶ Y)
    (φ : X.PartialIso Y) (θ : W.PartialIso X)
    (hθp : θ.IsOver p (𝟙 X)) (hθq : (θ.trans φ).IsOver q (𝟙 Y))
    (w : W) (hw : q w ∈ φ.target) :
    p w = φ.source.ι (φ.iso.inv ⟨q w,hw⟩) := by
  let V := θ.target ⊓ φ.source
  have hV : Dense (V : Set X) := θ.dense_target.inter_of_isOpen_right φ.dense_source φ.source.isOpen
  let α := θ.restrictTarget V hV inf_le_left
  let β := φ.restrictSource V hV inf_le_right
  let a : α.source.toScheme ⟶ φ.source.toScheme := α.iso.hom ≫ X.homOfLE inf_le_right
  have hp' : a ≫ φ.source.ι = α.source.ι ≫ p := by
    dsimp only [a]
    erw [Category.assoc,Scheme.homOfLE_ι]
    simpa only [Scheme.PartialIso.IsOver,Category.comp_id] using
      (hθp.restrictTarget V hV inf_le_left)
  have hq' : a ≫ φ.iso.hom ≫ φ.target.ι = α.source.ι ≫ q := by
    have hβ := restricted_partialIso_map φ V hV inf_le_right
    have hi : (X.isoOfEq (show α.target = β.source from rfl)).hom = 𝟙 V.toScheme :=
      congrArg Iso.hom (X.isoOfEq_rfl V)
    have hh : α.iso.hom ≫ β.iso.hom ≫ β.target.ι = α.source.ι ≫ q := by
      change α.iso.hom ≫ (X.isoOfEq (show α.target = β.source from rfl)).hom ≫
        β.iso.hom ≫ β.target.ι ≫ (𝟙 Y) = α.source.ι ≫ q at hθq
      erw [hi,Category.id_comp,Category.comp_id] at hθq
      exact hθq
    dsimp only [β] at hh
    erw [hβ] at hh
    exact hh
  let U := q ⁻¹ᵁ φ.target
  let qU : U.toScheme ⟶ φ.target.toScheme :=
    IsOpenImmersion.lift φ.target.ι (U.ι ≫ q) (by
      rintro _ ⟨x,rfl⟩
      exact ⟨⟨q x.1,x.2⟩,rfl⟩)
  have hsub : α.source ≤ U := by
    intro z hz
    have hh := congrArg (fun f : α.source.toScheme ⟶ Y => f ⟨z,hz⟩) hq'
    change q z ∈ φ.target
    change φ.target.ι (φ.iso.hom (a ⟨z,hz⟩)) = q z at hh
    rw [← hh]
    exact (φ.iso.hom (a ⟨z,hz⟩)).2
  let j := W.homOfLE hsub
  let : IsDominant j := Opens.isDominant_homOfLE α.dense_source hsub
  have hqU : qU ≫ φ.target.ι = U.ι ≫ q := IsOpenImmersion.lift_fac _ _ _
  have he : U.ι ≫ p = qU ≫ φ.iso.inv ≫ φ.source.ι := by
    apply ext_of_isDominant j
    have hj : j ≫ qU = a ≫ φ.iso.hom := by
      apply (cancel_mono φ.target.ι).mp
      rw [Category.assoc,hqU,← Category.assoc,
        show j ≫ U.ι = α.source.ι from W.homOfLE_ι hsub]
      exact hq'.symm
    rw [← Category.assoc,show j ≫ U.ι = α.source.ι from W.homOfLE_ι hsub,
      ← hp',← Category.assoc,← Category.assoc,hj]
    simp only [Category.assoc,Iso.hom_inv_id_assoc]
  have hh := congrArg (fun f : U.toScheme ⟶ X => f ⟨w,hw⟩) he
  have hqu : qU ⟨w,hw⟩ = ⟨q w,hw⟩ := by
    apply Subtype.ext
    exact congrArg (fun f : U.toScheme ⟶ Y => f ⟨w,hw⟩)
      (IsOpenImmersion.lift_fac φ.target.ι (U.ι ≫ q) _)
  change p w = φ.source.ι (φ.iso.inv (qU ⟨w,hw⟩)) at hh
  exact hh.trans (congrArg (fun z => φ.source.ι (φ.iso.inv z)) hqu)
lemma common_model_prime_noExtraction
    {W X Y : Scheme} [IsIntegral W] [X.IsSeparated]
    (p : W ⟶ X) (q : W ⟶ Y)
    (φ : X.PartialIso Y) (θ : W.PartialIso X)
    (hθp : θ.IsOver p (𝟙 X)) (hθq : (θ.trans φ).IsOver q (𝟙 Y))
    (hφ : NoExtractionOn φ) (F : PrimeDivisor W)
    (hF : Order.coheight (q F.1) = 1) :
    Order.coheight (p F.1) = 1 := by
  have hm := hφ ⟨q F.1,hF⟩
  let z : φ.target.toScheme := ⟨q F.1,hm⟩
  calc
    _ = Order.coheight (φ.source.ι (φ.iso.inv z)) :=
      congrArg Order.coheight (common_model_on_partial_locus p q φ θ hθp hθq F.1 hm)
    _ = Order.coheight (φ.iso.inv z) := coheight_eq_of_isOpenImmersion φ.source.ι
    _ = Order.coheight z := coheight_eq_of_isOpenImmersion φ.iso.inv
    _ = Order.coheight (q F.1) := (coheight_eq_of_isOpenImmersion (x := z) φ.target.ι).symm
    _ = 1 := hF
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma canonical_comparison_support_and_strictness {n : ℕ}
    (X Y : CanonicalModel n) (hX : IsSmoothNfold X.toComplexProjectiveVariety n)
    (hY : IsTerminalModel Y) (φ : X.scheme.PartialIso Y.scheme)
    (hφ : NoExtractionOn φ) (hbase : φ.IsOver X.structureMap Y.structureMap)
    (hc : CompatibleCanonicalData X Y φ hbase)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q] [IsProper p] [IsProper q]
    (hp : p ≫ X.structureMap = W.structureMap) (hq : q ≫ Y.structureMap = W.structureMap)
    (θ : W.scheme.PartialIso X.scheme) (hθp : θ.IsOver p (𝟙 X.scheme))
    (hθq : (θ.trans φ).IsOver q (𝟙 Y.scheme)) :
    ∃ P Q : QWeilDivisor W.scheme,
      IsQCartierPullback p (rationalWeilDivisor X.canonical) P ∧
      IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q ∧
      (∀ F : PrimeDivisor W.scheme, (P-Q) F ≠ 0 → 1 < Order.coheight (q F.1)) ∧
      (∀ F : PrimeDivisor W.scheme, Order.coheight (p F.1) = 1 →
        1 < Order.coheight (q F.1) → 0 < (P-Q) F) := by
  let : X.scheme.IsSeparated := ⟨by
    have h : IsSeparated (X.structureMap ≫ CategoryTheory.Limits.terminal.from _) := inferInstance
    simpa only [CategoryTheory.Limits.terminal.comp_from] using h⟩
  have hpb : IsBirationalMorphism p := ⟨θ,hθp⟩
  have hqb : IsBirationalMorphism q := ⟨θ.trans φ,hθq⟩
  obtain ⟨KW,hKp,hKq⟩ := exists_common_canonicalDivisor X Y φ hbase hc W hW p q hp hq θ hθp hθq
  obtain ⟨P,hP⟩ := exists_qCartierPullback p _ X.qCartier
  obtain ⟨Q,hQ⟩ := exists_qCartierPullback q _ Y.qCartier
  refine ⟨P,Q,hP,hQ,?_,?_⟩
  · intro F hF
    have hz : Order.coheight (q F.1) ≠ 0 := by
      intro he
      have hsp : q F.1 ⤳ genericPoint Y.scheme :=
        (Order.coheight_eq_zero.mp he) (genericPoint_specializes (q F.1))
      have heq := (hsp.antisymm (genericPoint_specializes (q F.1))).eq
      have hFη := birational_generic_fiber q hqb F.1 heq
      have h0 : Order.coheight F.1 = 0 := by
        rw [hFη]
        exact Order.coheight_eq_zero.mpr (fun x _ => genericPoint_specializes x)
      rw [F.2] at h0
      exact one_ne_zero h0
    apply lt_of_le_of_ne (Order.one_le_iff_ne_zero.mpr hz)
    intro he
    have hprime := common_model_prime_noExtraction p q φ θ hθp hθq hφ F he.symm
    have hP0 := relativeCanonical_vanishes_over_prime X W hW p hpb hp KW hKp P hP F hprime
    have hQ0 := relativeCanonical_vanishes_over_prime Y W hW q hqb hq KW hKq Q hQ F he.symm
    change (KW F : ℚ) - P F = 0 at hP0
    change (KW F : ℚ) - Q F = 0 at hQ0
    apply hF
    change P F - Q F = 0
    exact sub_eq_zero.mpr ((sub_eq_zero.mp hP0).symm.trans (sub_eq_zero.mp hQ0))
  · intro F hFp hFq
    exact canonical_comparison_strict_source_primes X Y hX hY W hW p q hpb hqb hp hq
      KW hKp hKq P Q hP hQ F hFp hFq
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma HasEffectiveCanonicalComparison.of_birational_morphism {n : ℕ}
    (X Y : CanonicalModel n) (hX : IsSmoothNfold X.toComplexProjectiveVariety n)
    (hY : IsTerminalModel Y) (φ : X.scheme.PartialIso Y.scheme)
    (hbase : φ.IsOver X.structureMap Y.structureMap)
    (hc : CompatibleCanonicalData X Y φ hbase)
    (f : X.scheme ⟶ Y.scheme) [IsDominant f] [IsProper f]
    (hf : f ≫ Y.structureMap = X.structureMap) (hreal : φ.IsOver f (𝟙 Y.scheme)) :
    HasEffectiveCanonicalComparison X Y φ := by
  have hfb : IsBirationalMorphism f := ⟨φ,hreal⟩
  have hform := (CompatibleCanonicalData.iff_morphism f hf φ hreal hbase).mp hc
  have hK : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n Y.form) X.canonical := by
    rw [← hform]
    exact X.canonical_of_form
  obtain ⟨Q,hQ⟩ := exists_qCartierPullback f _ Y.qCartier
  obtain ⟨hE,hsupp⟩ := relativeCanonical_effective_terminal Y hY X.toComplexProjectiveVariety hX
    f hfb hf X.canonical hK Q hQ
  have hi : (Scheme.PartialIso.refl X.scheme).IsOver (𝟙 X.scheme) (𝟙 X.scheme) :=
    Category.id_comp _
  have hi' : (Scheme.PartialIso.refl X.scheme).IsOver f f := Category.id_comp _
  refine ⟨X.toComplexProjectiveVariety,hX,𝟙 X.scheme,f,
    inferInstance,inferInstance,inferInstance,inferInstance,Category.id_comp _,hf,
    .refl X.scheme,hi,hi'.trans hreal,rationalWeilDivisor X.canonical,Q,
    rationalWeilDivisor X.canonical-Q,X.qCartier.pullback_id,hQ,?_,hE,?_,?_⟩
  · exact (add_sub_cancel _ _).symm
  · intro F hF
    exact (hsupp F).mp hF
  · intro F _ hF
    exact hY X.toComplexProjectiveVariety hX f inferInstance inferInstance hfb hf
      X.canonical hK Q hQ F hF
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
section
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
lemma IsQCartierPullback.add {f : X ⟶ Y} [IsDominant f]
    {D E : QWeilDivisor Y} {P Q : QWeilDivisor X}
    (hP : IsQCartierPullback f D P) (hQ : IsQCartierPullback f E Q) :
    IsQCartierPullback f (D+E) (P+Q) := by
  obtain ⟨m,hm,A,B,hA,hAD,hBP,hAB⟩ := hP
  obtain ⟨n,hn,C,G,hC,hCE,hGQ,hCG⟩ := hQ
  refine ⟨m*n,Nat.mul_pos hm hn,n • A + m • C,n • B + m • G,
    isCartierDivisor_add ((cartierDivisors (X := Y)).nsmul_mem hA n)
      ((cartierDivisors (X := Y)).nsmul_mem hC m),?_,?_,(hAB.nsmul n).add (hCG.nsmul m)⟩
  · ext p
    have hd := DFunLike.congr_fun hAD p
    have he := DFunLike.congr_fun hCE p
    change (m : ℚ) * D p = (A p : ℚ) at hd
    change (n : ℚ) * E p = (C p : ℚ) at he
    change ((m*n : ℕ) : ℚ) * (D p + E p) = ((n : ℤ) * A p + (m : ℤ) * C p : ℤ)
    push_cast
    rw [← hd,← he]
    ring
  · ext p
    have hp := DFunLike.congr_fun hBP p
    have hq := DFunLike.congr_fun hGQ p
    change (m : ℚ) * P p = (B p : ℚ) at hp
    change (n : ℚ) * Q p = (G p : ℚ) at hq
    change ((m*n : ℕ) : ℚ) * (P p + Q p) = ((n : ℤ) * B p + (m : ℤ) * G p : ℤ)
    push_cast
    rw [← hp,← hq]
    ring
lemma IsQCartierPullback.neg {f : X ⟶ Y} [IsDominant f]
    {D : QWeilDivisor Y} {P : QWeilDivisor X} (hP : IsQCartierPullback f D P) :
    IsQCartierPullback f (-D) (-P) := by
  obtain ⟨m,hm,A,B,hA,hAD,hBP,hAB⟩ := hP
  refine ⟨m,hm,-A,-B,isCartierDivisor_neg hA,?_,?_,hAB.neg⟩
  · ext p
    have h := DFunLike.congr_fun hAD p
    change (m : ℚ) * D p = (A p : ℚ) at h
    change (m : ℚ) * (-D p) = ((-A p : ℤ) : ℚ)
    simp only [Int.cast_neg,mul_neg,h]
  · ext p
    have h := DFunLike.congr_fun hBP p
    change (m : ℚ) * P p = (B p : ℚ) at h
    change (m : ℚ) * (-P p) = ((-B p : ℤ) : ℚ)
    simp only [Int.cast_neg,mul_neg,h]
lemma IsQCartierPullback.sub {f : X ⟶ Y} [IsDominant f]
    {D E : QWeilDivisor Y} {P Q : QWeilDivisor X}
    (hP : IsQCartierPullback f D P) (hQ : IsQCartierPullback f E Q) :
    IsQCartierPullback f (D-E) (P-Q) := by
  simpa only [sub_eq_add_neg] using hP.add hQ.neg
lemma IsQCartierPullback.mono [StalkwiseNormal X] [StalkwiseNormal Y]
    {f : X ⟶ Y} [IsDominant f]
    {D E : QWeilDivisor Y} {P Q : QWeilDivisor X}
    (hP : IsQCartierPullback f D P) (hQ : IsQCartierPullback f E Q) (hDE : D ≤ E) :
    P ≤ Q := by
  exact sub_nonneg.mp ((hQ.sub hP).nonneg (sub_nonneg.mpr hDE))
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

lemma rationalWeilDivisor_injective {X : Scheme} :
    Function.Injective (@rationalWeilDivisor X) := by
  intro D E h
  ext p
  have he : (D p : ℚ) = (E p : ℚ) := DFunLike.congr_fun h p
  exact_mod_cast he

lemma rationalWeilDivisor_nsmul {X : Scheme} (D : WeilDivisor X) (m : ℕ) :
    rationalWeilDivisor (m • D) = (m : ℚ) • rationalWeilDivisor D := by
  ext p
  change ((m • D p : ℤ) : ℚ) = (m : ℚ) * (D p : ℚ)
  simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

lemma multiples_cross_equal {X : Scheme} {D : QWeilDivisor X}
    {m n : ℕ} {A B : WeilDivisor X}
    (hA : (m : ℚ) • D = rationalWeilDivisor A)
    (hB : (n : ℚ) • D = rationalWeilDivisor B) : n • A = m • B := by
  apply rationalWeilDivisor_injective
  rw [rationalWeilDivisor_nsmul, rationalWeilDivisor_nsmul, ← hA, ← hB,
    smul_smul, smul_smul, mul_comm]

lemma cartierCurveDegree_nsmul {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    (D : cartierDivisors (X := X.scheme)) (C : CurveOn X) (m : ℕ) :
    cartierCurveDegree (m • D) C = m • cartierCurveDegree D C :=
  (cartierCurveDegreeHom C).map_nsmul m D

lemma isNefCartier_of_positive_multiple {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (D : cartierDivisors (X := X.scheme))
    {m : ℕ} (hm : 0 < m) (hD : IsNefCartier X (m • D)) : IsNefCartier X D := by
  intro C
  have h := hD C
  rw [cartierCurveDegree_nsmul, nsmul_eq_mul] at h
  exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hm)

theorem isNefQDivisor_iff_one_multiple
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D : QWeilDivisor X.scheme} (m : ℕ) (hm : 0 < m)
    (A : cartierDivisors (X := X.scheme))
    (hA : (m : ℚ) • D = rationalWeilDivisor A.1) :
    IsNefQDivisor X D ↔ IsNefCartier X A := by
  constructor
  · intro h
    exact h.2 m hm A.1 A.2 hA
  · intro h
    refine ⟨⟨m, hm, A.1, A.2, hA⟩, ?_⟩
    intro n _hn B hB heB C
    have he : n • A = m • (⟨B, hB⟩ : cartierDivisors) :=
      Subtype.ext (multiples_cross_equal hA heB)
    have hdeg := congrArg (fun T => cartierCurveDegree T C) he
    simp only [cartierCurveDegree_nsmul, nsmul_eq_mul] at hdeg
    have hnon : 0 ≤ (n : ℤ) * cartierCurveDegree A C := mul_nonneg (by positivity) (h C)
    rw [hdeg] at hnon
    exact nonneg_of_mul_nonneg_right hnon (by exact_mod_cast hm)

lemma isNefCartier_of_generated {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (D : cartierDivisors (X := X.scheme))
    (hD : ∀ x : X.scheme, IsGeneratedAt D.1 x) : IsNefCartier X D := by
  intro C
  exact cartierCurveDegree_nonneg_of_generatedAt D C (hD _)

lemma isNefCartier_of_isAmple {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (D : cartierDivisors (X := X.scheme))
    (hD : IsAmpleDivisor D.1) : IsNefCartier X D := by
  intro C
  obtain ⟨m, hm, s, hs, hsec, _, hnon, _⟩ :=
    hD.2 (C.morphism (genericPoint C.curve.scheme)) ⊤ trivial
  have hgen : IsGeneratedAt (m • D).1 (C.morphism (genericPoint C.curve.scheme)) :=
    ⟨s, hs, hsec, hnon⟩
  have h := cartierCurveDegree_nonneg_of_generatedAt (m • D) C hgen
  rw [cartierCurveDegree_nsmul, nsmul_eq_mul] at h
  exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hm)

theorem isNefQDivisor_of_isAmple
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    {D : QWeilDivisor X.scheme} (hD : IsAmpleQDivisor D) :
    IsNefQDivisor X D := by
  obtain ⟨m, hm, A, hA, heA⟩ := hD
  exact (isNefQDivisor_iff_one_multiple m hm ⟨A, hA.1⟩ heA).mpr
    (isNefCartier_of_isAmple ⟨A, hA.1⟩ hA)

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

structure CartierMultiple {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (D : QWeilDivisor X) where
  denominator : ℕ
  positive : 0 < denominator
  divisor : cartierDivisors (X := X)
  equation : (denominator : ℚ) • D = rationalWeilDivisor divisor.1

noncomputable def chooseCartierMultiple {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] {D : QWeilDivisor X} (hD : IsQCartierDivisor D) :
    CartierMultiple D := by
  choose m hm A hA he using hD
  exact ⟨m, hm, ⟨A, hA⟩, he⟩

noncomputable def CartierMultiple.degreeOn {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] {D : QWeilDivisor X.scheme}
    (M : CartierMultiple D) (C : CurveOn X) : ℚ :=
  (cartierCurveDegree M.divisor C : ℚ) / M.denominator

noncomputable def qCartierCurveDegree {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (D : QWeilDivisor X.scheme)
    (hD : IsQCartierDivisor D) (C : CurveOn X) : ℚ :=
  (chooseCartierMultiple hD).degreeOn C

end NumericalDimensionOne

end OAI
