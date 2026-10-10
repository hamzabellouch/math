import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.DivisorPresheaves
import OAI.AlgebraicGeometry.NumericalDimension.NormalCrossings

namespace OAI

/-! Multiplier Ideals. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits

namespace NumericalDimensionOne

noncomputable def ceilQWeilDivisor {X : Scheme} (D : QWeilDivisor X) : WeilDivisor X :=
  D.mapRange Int.ceil (by simp)

@[simp] lemma ceilQWeilDivisor_apply {X : Scheme} (D : QWeilDivisor X)
    (p : PrimeDivisor X) : ceilQWeilDivisor D p = ⌈D p⌉ := by
  rfl

theorem valuativeMultiplierIdeal_model_section {n : ℕ} (Y : CanonicalModel n)
    (Δ : QWeilDivisor Y.scheme)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    (f : W.scheme ⟶ Y.scheme) [IsDominant f]
    (hproper : IsProper f) (hbirational : IsBirationalMorphism f)
    (hf : f ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap f hf n Y.form) KW)
    (P : QWeilDivisor W.scheme)
    (hP : IsQCartierPullback f (rationalWeilDivisor Y.canonical + Δ) P)
    (U : Y.scheme.Opens) [Nonempty U] (a : Γ(Y.scheme,U))
    (ha : a ∈ valuativeMultiplierIdeal Y Δ U) :
    IsDivisorSectionOn (ceilQWeilDivisor (rationalWeilDivisor KW - P)) (f ⁻¹ᵁ U)
      (dominantFunctionFieldMap f (Y.scheme.germToFunctionField U a)) := by
  classical
  let : StalkwiseNormal W.scheme := smoothNormal W hW
  let b := dominantFunctionFieldMap f (Y.scheme.germToFunctionField U a)
  by_cases hb : b = 0
  · exact Or.inl hb
  right
  intro p hp
  let T : MultiplierDivisorialTest Y Δ :=
    { model := W, smooth := hW, map := f, dominant := inferInstance,
      proper := hproper, birational := hbirational, overBase := hf,
      canonical := KW, compatible := hKW, pullback := P, isPullback := hP,
      prime := p }
  have ht := (mem_valuativeMultiplierIdeal a).mp ha T hp
  have heq : algebraMap (W.scheme.presheaf.stalk p.1) W.scheme.functionField
      (T.regularMap hp a) = b := by
    dsimp only [MultiplierDivisorialTest.regularMap, RingHom.comp_apply, b, T]
    rw [← Y.scheme.algebraMap_germ_eq_germToFunctionField (x := f p.1) hp,
      dominantFunctionFieldMap_algebraMap]
  change MultiplierOrderCondition p ((rationalWeilDivisor KW - P) p)
    (T.regularMap hp a) at ht
  unfold MultiplierOrderCondition at ht
  rw [heq] at ht
  have hlt : -1 < (W.scheme.ord b p.1 : ℚ) + (rationalWeilDivisor KW - P) p :=
    ht.resolve_left hb
  have hceil : -W.scheme.ord b p.1 ≤ ⌈(rationalWeilDivisor KW - P) p⌉ := by
    rw [Int.le_ceil_iff]
    change -(W.scheme.ord b p.1 : ℚ) - 1 < (rationalWeilDivisor KW - P) p
    linarith
  change 0 ≤ W.scheme.ord b p.1 + ⌈(rationalWeilDivisor KW - P) p⌉
  omega

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits

namespace NumericalDimensionOne
noncomputable section
lemma divisorSectionOn_dominant_pullback
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] {D : WeilDivisor Y} {E : WeilDivisor X}
    (hE : IsCartierPullback f D E) {U : Y.Opens} {r : Y.functionField}
    (hr : IsDivisorSectionOn D U r) :
    IsDivisorSectionOn E (f ⁻¹ᵁ U) (dominantFunctionFieldMap f r) := by
  by_cases hr0 : r = 0
  · exact Or.inl (by simp [hr0])
  right
  intro p hp
  obtain ⟨V, hV, hpV, g, hg, hDg, hEg⟩ := hE p.1
  obtain ⟨W, hW, hpW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show f p.1 ∈ V ⊓ U from ⟨hpV, hp⟩)
  let : Nonempty W := ⟨⟨f p.1, hpW⟩⟩
  have hrW : IsDivisorSectionOn D W r :=
    hr.imp id (fun h q hq => h q (hWV hq).2)
  obtain ⟨a, ha⟩ := (cartier_local_section_iff hW hg
    (fun q hq => hDg q (hWV hq).1) r).mp hrW
  have hprod : 0 ≤ X.ord (dominantFunctionFieldMap f (r * g)) p.1 := by
    apply (ord_nonnegative_iff_regular p _ ((map_ne_zero _).mpr (mul_ne_zero hr0 hg))).mpr
    refine ⟨f.stalkMap p.1 (Y.presheaf.germ W (f p.1) hpW a), ?_⟩
    rw [← dominantFunctionFieldMap_algebraMap,
      Y.algebraMap_germ_eq_germToFunctionField, ha]
  rw [map_mul, X.ord_mul ((map_ne_zero _).mpr hr0) ((map_ne_zero _).mpr hg)] at hprod
  rwa [hEg p hpV]

lemma snc_model_section_discrepancy_bound
    (X Y : Scheme) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] [SmoothOfRelativeDimension n sY]
    (f : X ⟶ Y) [IsDominant f] (hf : f ≫ sY = sX)
    (ω : rationalTopForms (.of ℂ) sY n)
    (DX : WeilDivisor X) (DY : WeilDivisor Y)
    (hDX : IsCanonicalDivisorOf (.of ℂ) sX n
      (rationalTopFormPullback (.of ℂ) sX sY f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) sY n ω DY)
    {ι : Type*} [Fintype ι] (D : ι → WeilDivisor Y)
    (hD : IsSimpleNormalCrossingsDivisorFamilyOver Y sY n D)
    (c : ι → ℚ) (Q : QWeilDivisor X)
    (hQ : IsQCartierPullback f (rationalWeilDivisor DY + ∑ i, c i • rationalWeilDivisor (D i)) Q)
    (U : Y.Opens) (r : Y.functionField)
    (hr : IsDivisorSectionOn (ceilQWeilDivisor (-(∑ i, c i • rationalWeilDivisor (D i)))) U r)
    (p : PrimeDivisor X) (hp : f p.1 ∈ U) :
    dominantFunctionFieldMap f r = 0 ∨
      (-1 : ℚ) < (X.ord (dominantFunctionFieldMap f r) p.1 : ℚ) + (DX p : ℚ) - Q p := by
  classical
  by_cases hr0 : r = 0
  · exact Or.inl (by simp [hr0])
  right
  let A : WeilDivisor Y := ∑ i, ⌊c i⌋ • D i
  let Δ : QWeilDivisor Y := ∑ i, c i • rationalWeilDivisor (D i)
  let δ : QWeilDivisor Y := ∑ i, (c i - (⌊c i⌋ : ℚ)) • rationalWeilDivisor (D i)
  have hA : IsCartierDivisor A := (cartierDivisors (X := Y)).sum_mem
    (fun i _ => (cartierDivisors (X := Y)).zsmul_mem (hD.1 i).1 _)
  have hsplit : rationalWeilDivisor DY + δ =
      (rationalWeilDivisor DY + Δ) - rationalWeilDivisor A := by
    ext v
    simp only [δ, Δ, A, rationalWeilDivisor, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, Int.coe_castAddHom, Int.cast_sum, Int.cast_mul, sub_mul,
      Finset.sum_sub_distrib]
    ring
  have hlow (v : PrimeDivisor Y) : (A v : ℚ) ≤ Δ v := by
    dsimp [A, Δ, rationalWeilDivisor]
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, Int.cast_sum, Int.cast_mul]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
      (Int.floor_le (c i)) (by exact_mod_cast (hD.1 i).2 v))
  have hfloors : IsDivisorSectionOn (-A) U r := by
    right
    intro v hv
    have hvord := (hr.resolve_left hr0) v hv
    change 0 ≤ Y.ord r v.1 + ⌈-Δ v⌉ at hvord
    have hceil : -Y.ord r v.1 ≤ ⌈-Δ v⌉ := by omega
    rw [Int.le_ceil_iff] at hceil
    change -(Y.ord r v.1 : ℚ) - 1 < -Δ v at hceil
    have ha : (A v : ℚ) - (Y.ord r v.1 : ℚ) < 1 := by linarith [hlow v]
    have ha' : A v - Y.ord r v.1 < 1 := by exact_mod_cast ha
    change 0 ≤ Y.ord r v.1 - A v
    omega
  obtain ⟨P, hP⟩ := exists_cartierPullback f A hA
  have hsections := divisorSectionOn_dominant_pullback f hP.neg hfloors
  have hb : dominantFunctionFieldMap f r ≠ 0 := (map_ne_zero _).mpr hr0
  have horder := (hsections.resolve_left hb) p hp
  have horderQ : (P p : ℚ) ≤ (X.ord (dominantFunctionFieldMap f r) p.1 : ℚ) := by
    have horder' : P p ≤ X.ord (dominantFunctionFieldMap f r) p.1 := by
      change 0 ≤ X.ord (dominantFunctionFieldMap f r) p.1 - P p at horder
      omega
    exact_mod_cast horder'
  have hQ' : IsQCartierPullback f (rationalWeilDivisor DY + δ)
      (Q - rationalWeilDivisor P) := by
    rw [hsplit]
    exact hQ.sub (hP.rational hA)
  have ht := snc_fractional_discrepancy_bound_scheme X Y sX sY n f hf ω DX DY hDX hDY
    D hD (fun i => c i - (⌊c i⌋ : ℚ))
    (fun i => by linarith [Int.lt_floor_add_one (c i)]) _ hQ' p
  change (-1 : ℚ) < (DX p : ℚ) - (Q p - (P p : ℚ)) at ht
  linarith

end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open Opposite TopCat
open AlgebraicGeometry CategoryTheory TopCat Opposite TopologicalSpace
open CategoryTheory.Limits

namespace NumericalDimensionOne
noncomputable section
lemma canonical_coefficient_of_stalk_iso_scheme
    (X Y : Scheme) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n sY]
    (f : X ⟶ Y) [IsDominant f]
    (hf : f ≫ sY = sX)
    (ω : rationalTopForms (.of ℂ) sY n)
    (DX : WeilDivisor X) (DY : WeilDivisor Y)
    (hDX : IsCanonicalDivisorOf (.of ℂ) sX n
      (rationalTopFormPullback (.of ℂ) sX sY f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) sY n ω DY)
    (p : PrimeDivisor X) [IsIso (f.stalkMap p.1)]
    (hp : Order.coheight (f p.1) = 1) : DX p = DY ⟨f p.1,hp⟩ := by
  let := schemeStalkAlgebra (.of ℂ) sY (f p.1)
  let := schemeStalkAlgebra (.of ℂ) sX p.1
  let := schemeFieldAlgebra (.of ℂ) sY
  let := schemeFieldAlgebra (.of ℂ) sX
  let := stalk_field_scalar_tower (.of ℂ) sY (f p.1)
  let := stalk_field_scalar_tower (.of ℂ) sX p.1
  let : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  let : IsScalarTower ℂ Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar (.of ℂ) sX sY f hf a).symm)
  let : Algebra (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
    (f.stalkMap p.1).hom.toAlgebra
  let : IsScalarTower ℂ (Y.presheaf.stalk (f p.1))
      (X.presheaf.stalk p.1) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominant_stalk_scalar (.of ℂ) sX sY f hf p.1 a).symm)
  let : Algebra (Y.presheaf.stalk (f p.1)) X.functionField :=
    ((dominantFunctionFieldMap f).comp
      (algebraMap (Y.presheaf.stalk (f p.1)) Y.functionField)).toAlgebra
  let : IsScalarTower (Y.presheaf.stalk (f p.1))
      Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower (Y.presheaf.stalk (f p.1))
      (X.presheaf.stalk p.1) X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => dominantFunctionFieldMap_algebraMap f p.1 a)
  let : IsScalarTower ℂ (Y.presheaf.stalk (f p.1)) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap ℂ X.functionField a =
      dominantFunctionFieldMap f
        (algebraMap (Y.presheaf.stalk (f p.1)) Y.functionField
          (algebraMap ℂ (Y.presheaf.stalk (f p.1)) a))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominantFunctionFieldMap_scalar (.of ℂ) sX sY f hf a).symm
  let : Module.Free (Y.presheaf.stalk (f p.1))
      Ω[Y.presheaf.stalk (f p.1)⁄ℂ] :=
    smooth_stalk_differentials_free sY n (f p.1)
  let e := AlgEquiv.ofBijective
    (Algebra.ofId (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1))
    (ConcreteCategory.bijective_of_isIso (f.stalkMap p.1))
  let : Algebra.FormallyEtale (Y.presheaf.stalk (f p.1))
      (X.presheaf.stalk p.1) := Algebra.FormallyEtale.of_equiv e
  obtain ⟨b,a,ha,hω,hDYp⟩ := hDY.2 ⟨f p.1,hp⟩
  let bp := (topDifferential_isBaseChange ℂ (Y.presheaf.stalk (f p.1))
    (X.presheaf.stalk p.1) n).basis b
  have hωp : rationalTopFormPullback (.of ℂ) sX sY f hf n ω =
      dominantFunctionFieldMap f a • topDifferentialMap ℂ (X.presheaf.stalk p.1)
        X.functionField n (bp 0) := by
    change topDifferentialMap ℂ Y.functionField X.functionField n ω = _
    rw [hω,map_smul,← IsScalarTower.algebraMap_smul X.functionField a]
    rw [(topDifferential_isBaseChange ℂ (Y.presheaf.stalk (f p.1))
      (X.presheaf.stalk p.1) n).basis_apply]
    have h₁ := LinearMap.congr_fun (topDifferentialMap_comp ℂ
      (Y.presheaf.stalk (f p.1)) Y.functionField X.functionField n) (b 0)
    have h₂ := LinearMap.congr_fun (topDifferentialMap_comp ℂ
      (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1)
        X.functionField n) (b 0)
    exact congrArg (fun z => dominantFunctionFieldMap f a • z) (h₁.trans h₂.symm)
  obtain ⟨c,a',ha',hω',hDXp⟩ := hDX.2 p
  rw [hDXp,canonical_local_order_unique sX n p _ c bp a'
    (dominantFunctionFieldMap f a) hDX.1 ha' ((map_ne_zero _).mpr ha) hω' hωp,
    order_dominantFunctionFieldMap_of_stalk_iso f p hp a ha,hDYp]
lemma exists_canonicalDivisorOf_nonzero_scheme
    (W : Scheme) [IsIntegral W] [IsLocallyNoetherian W] [CompactSpace W]
    (sW : W ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n sW]
    (ω : rationalTopForms (.of ℂ) sW n) (hω : ω ≠ 0) :
    ∃ KW : WeilDivisor W, IsCanonicalDivisorOf (.of ℂ) sW n ω KW := by
  obtain ⟨D,η,hD⟩ := exists_canonicalDivisor_of_smooth sW n
  let := schemeFieldAlgebra (.of ℂ) sW
  obtain ⟨b⟩ := nonempty_smooth_canonical_field_basis sW n
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
  simpa only [heq] using canonicalDivisorOf_smul sW n hD (div_ne_zero ha' ha)

theorem lift_near_prime_divisor_of_proper_birational
    {T W Y : Scheme} [IsIntegral T] [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian T] [StalkwiseNormal T]
    (f : T ⟶ Y) [IsDominant f] (π : W ⟶ Y) [IsProper π]
    (φ : W.PartialIso Y) (hφ : φ.IsOver π (𝟙 Y)) (p : PrimeDivisor T) :
    ∃ (U : T.Opens), p.1 ∈ U ∧ ∃ (g : U.toScheme ⟶ W),
      g ≫ π = U.ι ≫ f ∧ IsDominant g
 := by
  have : IsDiscreteValuationRing (T.presheaf.stalk p.1) := dvr_at_prime_divisor p
  have hgeneric : genericPoint T ∈ f ⁻¹ᵁ φ.target := by
    change f (genericPoint T) ∈ φ.target
    rw [dominant_genericPoint f]
    exact ((genericPoint_spec Y).mem_open_set_iff φ.target.isOpen).mpr
      (by simpa using φ.dense_target.nonempty)
  let V := f ⁻¹ᵁ φ.target
  let a := V.fromSpecStalkOfMem (genericPoint T) hgeneric ≫ (f ∣_ φ.target)
  have ha : a ≫ φ.target.ι = T.fromSpecStalk (genericPoint T) ≫ f := by
    dsimp only [a]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
    exact congrArg (fun z => z ≫ f) (V.fromSpecStalkOfMem_ι _ _)
  have : IsDominant (a ≫ φ.target.ι) := ha ▸ inferInstance
  have : IsDominant a := IsDominant.of_comp_of_isOpenImmersion a φ.target.ι
  have : IsDominant φ.source.ι := Opens.isDominant_ι φ.dense_source
  let g := a ≫ φ.iso.inv ≫ φ.source.ι
  have : IsDominant g := inferInstance
  have hg : g ≫ π = T.fromSpecStalk (genericPoint T) ≫ f := by
    have hinv : φ.iso.inv ≫ φ.source.ι ≫ π = φ.target.ι := by
      simpa [Scheme.PartialIso.IsOver, Scheme.PartialIso.symm] using hφ.symm
    simpa only [g, Category.assoc, hinv] using ha
  have hv : ValuativeCriterion.Existence π := by
    have h : UniversallyClosed π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let j := Spec.map (CommRingCat.ofHom
    (algebraMap (T.presheaf.stalk p.1) T.functionField))
  have hw : g ≫ π = j ≫ (T.fromSpecStalk p.1 ≫ f) := by
    rw [hg, ← Category.assoc]
    congr 1
    exact (T.SpecMap_stalkSpecializes_fromSpecStalk
      ((genericPoint_spec T).specializes trivial)).symm
  obtain ⟨l, hl₁, hl₂⟩ := (hv {
    R := T.presheaf.stalk p.1
    commRing := inferInstanceAs (CommRing (T.presheaf.stalk p.1))
    domain := inferInstanceAs (IsDomain (T.presheaf.stalk p.1))
    K := T.functionField
    i₁ := g
    i₂ := T.fromSpecStalk p.1 ≫ f
    commSq := ⟨hw⟩ }).exists_lift
  obtain ⟨U, hpU, s, hls, hs⟩ := spread_out_of_isGermInjective' f π l hl₂
  have hfactor : (j ≫ U.fromSpecStalkOfMem p.1 hpU) ≫ s = g := by
    rw [Category.assoc, ← hls]
    exact hl₁
  have : IsDominant ((j ≫ U.fromSpecStalkOfMem p.1 hpU) ≫ s) := hfactor ▸ inferInstance
  have : IsDominant s := IsDominant.of_comp (j ≫ U.fromSpecStalkOfMem p.1 hpU) s
  exact ⟨U, hpU, s, hs, inferInstance⟩

lemma MultiplierDivisorialTest.regularMap_fraction {n : ℕ} {Y : CanonicalModel n}
    {Δ : QWeilDivisor Y.scheme} (T : MultiplierDivisorialTest Y Δ)
    {U : Y.scheme.Opens} [Nonempty U] (hp : T.map T.prime.1 ∈ U) (a : Γ(Y.scheme,U)) :
    letI := T.dominant
    algebraMap (T.model.scheme.presheaf.stalk T.prime.1) T.model.scheme.functionField
      (T.regularMap hp a) = dominantFunctionFieldMap T.map (Y.scheme.germToFunctionField U a) := by
  let := T.dominant
  dsimp only [MultiplierDivisorialTest.regularMap, RingHom.comp_apply]
  rw [← dominantFunctionFieldMap_algebraMap,
    Y.scheme.algebraMap_germ_eq_germToFunctionField hp a]

lemma valuativeMultiplierIdeal_identity_inequality {n : ℕ}
    (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (Δ : QWeilDivisor Y.scheme) (hQ : IsQCartierDivisor (rationalWeilDivisor Y.canonical + Δ))
    (U : Y.scheme.Opens) [Nonempty U] (a : Γ(Y.scheme,U))
    (ha : a ∈ valuativeMultiplierIdeal Y Δ U) :
    Y.scheme.germToFunctionField U a = 0 ∨
      ∀ p : PrimeDivisor Y.scheme, p.1 ∈ U →
        -1 < (Y.scheme.ord (Y.scheme.germToFunctionField U a) p.1 : ℚ) - Δ p := by
  classical
  by_cases hz : Y.scheme.germToFunctionField U a = 0
  · exact Or.inl hz
  right
  intro p hp
  let T : MultiplierDivisorialTest Y Δ :=
    { model := Y.toComplexProjectiveVariety, smooth := hY, map := 𝟙 Y.scheme,
      dominant := inferInstance, proper := inferInstance,
      birational := ⟨.refl Y.scheme, Category.id_comp _⟩,
      overBase := Category.id_comp _, canonical := Y.canonical,
      compatible := by rw [rationalTopFormPullback_id]; exact Y.canonical_of_form,
      pullback := rationalWeilDivisor Y.canonical + Δ,
      isPullback := hQ.pullback_id, prime := p }
  have ht := (mem_valuativeMultiplierIdeal a).mp ha T hp
  change MultiplierOrderCondition p _ (T.regularMap hp a) at ht
  unfold MultiplierOrderCondition at ht
  rw [T.regularMap_fraction hp a] at ht
  have he : dominantFunctionFieldMap T.map (Y.scheme.germToFunctionField U a) =
      Y.scheme.germToFunctionField U a := dominantFunctionFieldMap_id_apply _
  rw [he] at ht
  have hlt := ht.resolve_left hz
  change (-1 : ℚ) < (Y.scheme.ord _ p.1 : ℚ) +
    ((Y.canonical p : ℚ) - ((Y.canonical p : ℚ) + Δ p)) at hlt
  linarith

theorem mem_valuativeMultiplierIdeal_iff_section_on_snc_model
    {n : ℕ} (Y : CanonicalModel n) (Δ : QWeilDivisor Y.scheme)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    [StalkwiseNormal W.scheme]
    (π : W.scheme ⟶ Y.scheme) [IsDominant π] [IsProper π]
    (hbir : IsBirationalMorphism π) (hπ : π ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback π (rationalWeilDivisor Y.canonical + Δ) Q)
    {ι : Type*} [Fintype ι] (D : ι → WeilDivisor W.scheme)
    (hD : IsSimpleNormalCrossingsDivisorFamily W n D) (c : ι → ℚ)
    (hSNC : Q - rationalWeilDivisor KW = ∑ i, c i • rationalWeilDivisor (D i))
    (U : Y.scheme.Opens) [Nonempty U] (a : Γ(Y.scheme,U)) :
    a ∈ valuativeMultiplierIdeal Y Δ U ↔
      IsDivisorSectionOn (ceilQWeilDivisor (rationalWeilDivisor KW - Q)) (π ⁻¹ᵁ U)
        (dominantFunctionFieldMap π (Y.scheme.germToFunctionField U a))
 := by
  classical
  constructor
  · intro ha
    exact valuativeMultiplierIdeal_model_section Y Δ W hW π inferInstance hbir hπ KW hKW Q hQ U a ha
  · intro ha
    apply (mem_valuativeMultiplierIdeal a).mpr
    intro T hp
    let := T.dominant
    let : StalkwiseNormal T.model.scheme := smoothNormal T.model T.smooth
    let r := Y.scheme.germToFunctionField U a
    let rT := dominantFunctionFieldMap T.map r
    have heq := T.regularMap_fraction hp a
    change MultiplierOrderCondition T.prime T.discrepancy (T.regularMap hp a)
    unfold MultiplierOrderCondition
    rw [heq]
    by_cases hrT : rT = 0
    · exact Or.inl hrT
    right
    obtain ⟨φ, hφ⟩ := hbir
    obtain ⟨V, hpV, g, hgπ, hgdom⟩ :=
      lift_near_prime_divisor_of_proper_birational T.map π φ hφ T.prime
    let : Nonempty V := ⟨⟨T.prime.1, hpV⟩⟩
    let : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨T.prime.1, hpV⟩)
    let : IsDominant g := hgdom
    let : AlgebraicGeometry.IsNoetherian T.model.scheme := {}
    let : NoetherianSpace V := NoetherianSpace.set (V : Set T.model.scheme)
    let : CompactSpace V.toScheme := inferInstanceAs (CompactSpace V)
    let : SmoothOfRelativeDimension n T.model.structureMap := T.smooth
    let : SmoothOfRelativeDimension n W.structureMap := hW
    let sV := V.ι ≫ T.model.structureMap
    let : SmoothOfRelativeDimension n sV := by
      dsimp only [sV]
      simpa only [zero_add] using
        (inferInstance : SmoothOfRelativeDimension (0 + n) (V.ι ≫ T.model.structureMap))
    let : Smooth sV := SmoothOfRelativeDimension.smooth n sV
    let : StalkwiseNormal V.toScheme :=
      ⟨integrallyClosed_stalk_of_smooth_field sV⟩
    let pV : PrimeDivisor V.toScheme := ⟨⟨T.prime.1, hpV⟩, by
      have h := coheight_eq_of_isOpenImmersion (x := (⟨T.prime.1, hpV⟩ : V)) V.ι
      exact h.symm.trans T.prime.2⟩
    have hbase : g ≫ W.structureMap = sV := by
      rw [← hπ, ← Category.assoc, hgπ, Category.assoc, T.overBase]
    let ωT := rationalTopFormPullback (.of ℂ) T.model.structureMap Y.structureMap
      T.map T.overBase n Y.form
    let ωV := rationalTopFormPullback (.of ℂ) sV T.model.structureMap V.ι rfl n ωT
    have hVbir : IsBirationalMorphism V.ι :=
      V.ι.birationalOver (𝟙 T.model.scheme) V.ι (Category.comp_id _)
    have hωV : ωV ≠ 0 := by
      intro hz
      apply T.compatible.1
      apply (rationalTopFormPullback_birational_bijective sV T.model.structureMap
        V.ι hVbir rfl n).1
      exact hz.trans (by simp only [rationalTopFormPullback, map_zero])
    obtain ⟨KV, hKV⟩ := exists_canonicalDivisorOf_nonzero_scheme V.toScheme sV n ωV hωV
    have hforms : rationalTopFormPullback (.of ℂ) sV W.structureMap g hbase n
        (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) = ωV := by
      rw [← rationalTopFormPullback_comp (.of ℂ) sV W.structureMap Y.structureMap
        g π hbase hπ n Y.form]
      dsimp only [ωV, ωT]
      rw [← rationalTopFormPullback_comp (.of ℂ) sV T.model.structureMap Y.structureMap
        V.ι T.map rfl T.overBase n Y.form]
      exact congrFun (rationalTopFormPullback_congr (.of ℂ) sV Y.structureMap
        (g ≫ π) (V.ι ≫ T.map) _ _ hgπ n) Y.form
    have hKVg : IsCanonicalDivisorOf (.of ℂ) sV n
        (rationalTopFormPullback (.of ℂ) sV W.structureMap g hbase n
          (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form)) KV := by
      rw [hforms]
      exact hKV
    obtain ⟨P, hP⟩ := exists_qCartierPullback g Q hQ.isQCartier
    obtain ⟨R, hR⟩ := exists_qCartierPullback V.ι T.pullback T.isPullback.isQCartier
    have hPc := hQ.comp hP
    have hRc := T.isPullback.comp hR
    have hPR : P = R := by
      simp only [hgπ] at hPc
      exact hPc.unique hRc
    have hQeq : Q = rationalWeilDivisor KW + ∑ i, c i • rationalWeilDivisor (D i) := by
      rw [← hSNC]
      abel
    have hP' : IsQCartierPullback g
        (rationalWeilDivisor KW + ∑ i, c i • rationalWeilDivisor (D i)) P := by
      rw [← hQeq]
      exact hP
    have hneg : rationalWeilDivisor KW - Q = -(∑ i, c i • rationalWeilDivisor (D i)) := by
      rw [← hSNC]
      abel
    have ha' : IsDivisorSectionOn
        (ceilQWeilDivisor (-(∑ i, c i • rationalWeilDivisor (D i)))) (π ⁻¹ᵁ U)
        (dominantFunctionFieldMap π r) := by
      rw [← hneg]
      exact ha
    have hp' : g pV.1 ∈ π ⁻¹ᵁ U := by
      change π (g pV.1) ∈ U
      rw [← Scheme.Hom.comp_apply, hgπ, Scheme.Hom.comp_apply]
      exact hp
    have hbound := snc_model_section_discrepancy_bound V.toScheme W.scheme sV W.structureMap n
      g hbase _ KV KW hKVg hKW D hD c P hP' (π ⁻¹ᵁ U)
      (dominantFunctionFieldMap π r) ha' pV hp'
    have hfrac : dominantFunctionFieldMap g (dominantFunctionFieldMap π r) =
        dominantFunctionFieldMap V.ι rT := by
      rw [← dominantFunctionFieldMap_comp_apply]
      simp only [hgπ, dominantFunctionFieldMap_comp_apply, rT]
    rw [hfrac] at hbound
    have hrV : dominantFunctionFieldMap V.ι rT ≠ 0 := (map_ne_zero _).mpr hrT
    have hbound' := hbound.resolve_left hrV
    have hKVcoeff : KV pV = T.canonical T.prime := by
      exact canonical_coefficient_of_stalk_iso_scheme V.toScheme T.model.scheme sV
        T.model.structureMap n V.ι rfl ωT KV T.canonical hKV T.compatible pV T.prime.2
    have hPcoeff : P pV = T.pullback T.prime := by
      rw [hPR]
      exact hR.coeff_eq_of_stalk_iso V.ι pV T.prime.2
    have hord : V.toScheme.ord (dominantFunctionFieldMap V.ι rT) pV.1 =
        T.model.scheme.ord rT T.prime.1 :=
      order_dominantFunctionFieldMap_of_stalk_iso V.ι pV T.prime.2 rT hrT
    rw [hord, hKVcoeff, hPcoeff] at hbound'
    change (-1 : ℚ) < (T.model.scheme.ord rT T.prime.1 : ℚ) +
      ((T.canonical T.prime : ℚ) - T.pullback T.prime)
    linarith

end
end NumericalDimensionOne

end OAI
