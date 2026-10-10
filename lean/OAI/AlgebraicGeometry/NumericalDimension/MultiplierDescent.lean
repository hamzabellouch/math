import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.MultiplierIdeals
import OAI.AlgebraicGeometry.NumericalDimension.MultiplierSheaves

namespace OAI

/-! Multiplier Descent. -/

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

lemma open_regular_iff_nonnegative_orders
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
    (U : X.Opens) [Nonempty U] (f : X.functionField) :
    (∃ a : Γ(X,U), X.germToFunctionField U a = f) ↔
      (f = 0 ∨ ∀ p : PrimeDivisor X, p.1 ∈ U → 0 ≤ X.ord f p.1) := by
  classical
  constructor
  · rintro ⟨a,rfl⟩
    by_cases hf : X.germToFunctionField U a = 0
    · exact Or.inl hf
    right
    intro p hp
    apply (ord_nonnegative_iff_regular p _ hf).mpr
    exact ⟨X.presheaf.germ U p.1 hp a, X.algebraMap_germ_eq_germToFunctionField hp a⟩
  · rintro (rfl | h)
    · exact ⟨0, map_zero _⟩
    have haff : ∀ x : U, ∃ V : X.Opens, IsAffineOpen V ∧ x.1 ∈ V ∧ V ≤ U :=
      fun x => exists_isAffineOpen_mem_and_subset x.2
    choose V hV hxV hVU using haff
    let (x : U) : Nonempty (V x) := ⟨⟨x.1,hxV x⟩⟩
    have hgV (x : U) : genericPoint X ∈ V x :=
      ((genericPoint_spec X).mem_open_set_iff (V x).isOpen).mpr
        (by simpa using (inferInstance : Nonempty (V x)))
    have hlocal (x : U) : ∃ a : Γ(X,V x), X.germToFunctionField (V x) a = f :=
      (affine_regular_iff_nonnegative_orders (hV x) f).mpr
        (Or.inr fun p hp => h p (hVU x hp))
    choose sf hsf using hlocal
    have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
      intro x y
      let : Nonempty (V x ⊓ V y : X.Opens) := ⟨⟨genericPoint X,hgV x,hgV y⟩⟩
      apply X.germToFunctionField_injective (V x ⊓ V y)
      rw [germToFunctionField_restrict, germToFunctionField_restrict, hsf, hsf]
    have hcover : U ≤ ⨆ x : U, V x := by
      intro x hx
      exact Opens.mem_iSup.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
    obtain ⟨a,ha,_⟩ := X.sheaf.existsUnique_gluing' V U
      (fun x => homOfLE (hVU x)) hcover sf hcompatible
    refine ⟨a,?_⟩
    let x : U := Classical.arbitrary U
    have hax : X.presheaf.map (homOfLE (hVU x)).op a = sf x := ha x
    rw [← germToFunctionField_restrict (U := V x) (homOfLE (hVU x)) a, hax, hsf x]

lemma roundup_section_descends_regular
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (Δ : QWeilDivisor Y.scheme) (hΔ : 0 ≤ Δ)
    (W : ComplexProjectiveVariety) (π : W.scheme ⟶ Y.scheme)
    [IsDominant π] [IsProper π] (hbir : IsBirationalMorphism π)
    (hπ : π ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback π (rationalWeilDivisor Y.canonical + Δ) Q)
    (U : Y.scheme.Opens) [Nonempty U] (f : Y.scheme.functionField)
    (hsec : IsDivisorSectionOn (ceilQWeilDivisor (rationalWeilDivisor KW - Q))
      (π ⁻¹ᵁ U) (dominantFunctionFieldMap π f)) :
    ∃ a : Γ(Y.scheme,U), Y.scheme.germToFunctionField U a = f := by
  apply (open_regular_iff_nonnegative_orders U f).mpr
  by_cases hf : f = 0
  · exact Or.inl hf
  right
  intro p hpU
  obtain ⟨q,hq,hiso,_⟩ := exists_unique_prime_over_of_proper_birational π hbir p
  let : IsIso (π.stalkMap q.1) := hiso
  have hpq : Order.coheight (π q.1) = 1 := by rw [hq]; exact p.2
  have heqp : (⟨π q.1,hpq⟩ : PrimeDivisor Y.scheme) = p := Subtype.ext hq
  have hKcoeff := canonical_coefficient_of_stalk_iso W Y.toComplexProjectiveVariety n
    hY π hπ Y.form KW Y.canonical hKW Y.canonical_of_form q hpq
  rw [heqp] at hKcoeff
  have hQcoeff := hQ.coeff_eq_of_stalk_iso π q hpq
  rw [heqp] at hQcoeff
  have hdiff : (rationalWeilDivisor KW - Q) q = -Δ p := by
    change (KW q : ℚ) - Q q = _
    rw [hKcoeff,hQcoeff]
    change (Y.canonical p : ℚ) - ((Y.canonical p : ℚ) + Δ p) = _
    ring
  have hceil : ceilQWeilDivisor (rationalWeilDivisor KW - Q) q ≤ 0 := by
    rw [ceilQWeilDivisor_apply,hdiff]
    exact Int.ceil_nonpos.mpr (neg_nonpos.mpr (hΔ p))
  have hqU : q.1 ∈ π ⁻¹ᵁ U := by change π q.1 ∈ U; rw [hq]; exact hpU
  have hnonzero : dominantFunctionFieldMap π f ≠ 0 := (map_ne_zero _).mpr hf
  have horder := hsec.resolve_left hnonzero q hqU
  have hord := order_dominantFunctionFieldMap_of_stalk_iso π q hpq f hf
  rw [hq] at hord
  rw [hord] at horder
  omega

theorem multiplier_sections_iff_roundup_sections
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (Δ : QWeilDivisor Y.scheme) (hΔ : 0 ≤ Δ)
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
    (U : Y.scheme.Opens) [Nonempty U] (r : W.scheme.functionField) :
    (∃ a : Γ(Y.scheme,U), a ∈ valuativeMultiplierIdeal Y Δ U ∧
      dominantFunctionFieldMap π (Y.scheme.germToFunctionField U a) = r) ↔
      IsDivisorSectionOn (ceilQWeilDivisor (rationalWeilDivisor KW - Q)) (π ⁻¹ᵁ U) r
 := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (mem_valuativeMultiplierIdeal_iff_section_on_snc_model Y Δ W hW π hbir hπ
      KW hKW Q hQ D hD c hSNC U a).mp ha
  · intro hr
    obtain ⟨φ,hφ⟩ := hbir
    let f := partialIsoFunctionFieldEquiv φ r
    have hf : dominantFunctionFieldMap π f = r := by
      apply (partialIsoFunctionFieldEquiv φ).injective
      exact partialIso_dominantFunctionFieldMap π φ hφ f
    have hr' : IsDivisorSectionOn (ceilQWeilDivisor (rationalWeilDivisor KW - Q))
        (π ⁻¹ᵁ U) (dominantFunctionFieldMap π f) := hf.symm ▸ hr
    obtain ⟨a,ha⟩ := roundup_section_descends_regular Y hY Δ hΔ W π
      ⟨φ,hφ⟩ hπ KW hKW Q hQ U f hr'
    refine ⟨a,?_,?_⟩
    · apply (mem_valuativeMultiplierIdeal_iff_section_on_snc_model Y Δ W hW π
        ⟨φ,hφ⟩ hπ KW hKW Q hQ D hD c hSNC U a).mpr
      rwa [ha]
    · rw [ha,hf]

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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat

namespace NumericalDimensionOne

lemma regularFunctionValues_pullback {X Y : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] (U : Y.Opens) (a : Γ(Y,U)) (x : f ⁻¹ᵁ U) :
    regularFunctionValues (f ⁻¹ᵁ U) (f.app U a) x =
      dominantFunctionFieldMap f (regularFunctionValues U a ⟨f x.1,x.2⟩) := by
  change algebraMap (X.presheaf.stalk x.1) X.functionField
      (X.presheaf.germ (f ⁻¹ᵁ U) x.1 x.2 (f.app U a)) =
    dominantFunctionFieldMap f
      (algebraMap (Y.presheaf.stalk (f x.1)) Y.functionField
        (Y.presheaf.germ U (f x.1) x.2 a))
  rw [dominantFunctionFieldMap_algebraMap]
  exact congrArg (algebraMap (X.presheaf.stalk x.1) X.functionField)
    (f.germ_stalkMap_apply U x.1 (show f x.1 ∈ U from x.2) a).symm

section
variable {n : ℕ} (Y : CanonicalModel n) (Δ : QWeilDivisor Y.scheme)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    [StalkwiseNormal W.scheme]
    (π : W.scheme ⟶ Y.scheme) [IsDominant π] [IsProper π]
    (hbir : IsBirationalMorphism π) (hπ : π ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKW : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap π hπ n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback π (rationalWeilDivisor Y.canonical + Δ) Q)

noncomputable def multiplierToRoundupApp (U : Y.scheme.Opens) :
    (multiplierModulePresheaf Y Δ).obj (op U) ⟶
      ((SheafOfModules.pushforward π.toRingCatSheafHom).obj
        (divisorModuleSheaf (ceilQWeilDivisor (rationalWeilDivisor KW - Q)))).val.obj (op U) :=
  ModuleCat.ofHom (R := Γ(Y.scheme,U))
    (X := ModuleCat.of Γ(Y.scheme,U) (valuativeMultiplierIdeal Y Δ U))
    (Y := (ModuleCat.restrictScalars (π.app U).hom).obj
      (ModuleCat.of Γ(W.scheme,π ⁻¹ᵁ U)
        (divisorFunctionSubmodule (ceilQWeilDivisor (rationalWeilDivisor KW - Q)) (π ⁻¹ᵁ U)))) {
    toFun := fun a => ⟨fun x => dominantFunctionFieldMap π
      (regularFunctionValues U a.1 ⟨π x.1,x.2⟩), by
      classical
      by_cases hU : Nonempty U
      · let := hU
        have hh : (divisorFunctionPrelocal (ceilQWeilDivisor (rationalWeilDivisor KW - Q))).pred
            (fun x : π ⁻¹ᵁ U => dominantFunctionFieldMap π
              (regularFunctionValues U a.1 ⟨π x.1,x.2⟩)) := by
          refine ⟨dominantFunctionFieldMap π (Y.scheme.germToFunctionField U a.1),?_,?_⟩
          · intro x
            exact congrArg (dominantFunctionFieldMap π)
              (regularFunctionValues_eq U a.1 ⟨π x.1,x.2⟩)
          · exact valuativeMultiplierIdeal_model_section Y Δ W hW π inferInstance
              hbir hπ KW hKW Q hQ U a.1 a.2
        exact PrelocalPredicate.sheafifyOf hh
      · have heq : (fun x : π ⁻¹ᵁ U => dominantFunctionFieldMap π
            (regularFunctionValues U a.1 ⟨π x.1,x.2⟩)) = 0 := by
          funext x
          exact (hU ⟨⟨π x.1,x.2⟩⟩).elim
        rw [heq]
        exact divisorFunctionLocal_zero _ _⟩
    map_add' := by
      intro a b
      apply Subtype.ext
      funext x
      change dominantFunctionFieldMap π
        (regularFunctionValues U (a.1+b.1) ⟨π x.1,x.2⟩) =
        dominantFunctionFieldMap π (regularFunctionValues U a.1 ⟨π x.1,x.2⟩) +
          dominantFunctionFieldMap π (regularFunctionValues U b.1 ⟨π x.1,x.2⟩)
      simp only [map_add, Pi.add_apply]
    map_smul' := by
      intro a b
      apply Subtype.ext
      funext x
      change dominantFunctionFieldMap π
        (regularFunctionValues U (a*b.1) ⟨π x.1,x.2⟩) =
        regularFunctionValues (π ⁻¹ᵁ U) (π.app U a) x *
          dominantFunctionFieldMap π (regularFunctionValues U b.1 ⟨π x.1,x.2⟩)
      rw [regularFunctionValues_pullback]
      simp only [map_mul, Pi.mul_apply] }

noncomputable def multiplierToRoundup : multiplierModuleSheaf Y Δ ⟶
    (SheafOfModules.pushforward π.toRingCatSheafHom).obj
      (divisorModuleSheaf (ceilQWeilDivisor (rationalWeilDivisor KW - Q))) where
  val := {
    app := fun U => multiplierToRoundupApp Y Δ W hW π hbir hπ KW hKW Q hQ U.unop
    naturality := by
      intro U V i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      funext x
      change dominantFunctionFieldMap π
          (regularFunctionValues V.unop (Y.scheme.presheaf.map i a.1) ⟨π x.1,x.2⟩) =
        dominantFunctionFieldMap π
          (regularFunctionValues U.unop a.1 (i.unop ⟨π x.1,x.2⟩))
      exact congrArg (dominantFunctionFieldMap π)
        (regularFunctionValues_res i.unop a.1 ⟨π x.1,x.2⟩) }
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat

namespace NumericalDimensionOne
lemma multiplierToRoundupApp_bijective
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (Δ : QWeilDivisor Y.scheme) (hΔ : 0 ≤ Δ)
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
    (U : Y.scheme.Opens) :
    Function.Bijective (multiplierToRoundupApp Y Δ W hW π hbir hπ KW hKW Q hQ U).hom := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    have hη : genericPoint Y.scheme ∈ U :=
      (genericPoint_specializes (Classical.arbitrary U).1).mem_open U.isOpen
        (Classical.arbitrary U).2
    have hηW : genericPoint W.scheme ∈ π ⁻¹ᵁ U := by
      change π (genericPoint W.scheme) ∈ U
      rwa [dominant_genericPoint π]
    let x : π ⁻¹ᵁ U := ⟨genericPoint W.scheme,hηW⟩
    let : Nonempty (π ⁻¹ᵁ U) := ⟨x⟩
    constructor
    · intro a b hab
      apply Subtype.ext
      apply Y.scheme.germToFunctionField_injective U
      apply (dominantFunctionFieldMap π).injective
      have h := congrArg (fun z => z.1 x) hab
      change dominantFunctionFieldMap π (regularFunctionValues U a.1 ⟨π x.1,x.2⟩) =
        dominantFunctionFieldMap π (regularFunctionValues U b.1 ⟨π x.1,x.2⟩) at h
      simpa only [regularFunctionValues_eq] using h
    · intro s
      obtain ⟨r,hr,hs⟩ := (divisorFunctionLocal_iff (U := π ⁻¹ᵁ U) s.1).mp s.2
      obtain ⟨a,ha,hpull⟩ := (multiplier_sections_iff_roundup_sections Y hY Δ hΔ
        W hW π hbir hπ KW hKW Q hQ D hD c hSNC U r).mpr hs
      refine ⟨⟨a,ha⟩,?_⟩
      apply Subtype.ext
      funext x
      change dominantFunctionFieldMap π (regularFunctionValues U a ⟨π x.1,x.2⟩) = s.1 x
      rw [regularFunctionValues_eq,hpull,hr]
  · constructor
    · intro a b _
      apply Subtype.ext
      apply TopCat.Presheaf.section_ext Y.scheme.sheaf U a.1 b.1
      intro x hx
      exact (hU ⟨⟨x,hx⟩⟩).elim
    · intro s
      refine ⟨0,?_⟩
      apply Subtype.ext
      funext x
      exact (hU ⟨⟨π x.1,x.2⟩⟩).elim
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat

namespace NumericalDimensionOne

theorem multiplierModuleSheaf_iso_pushforward_on_snc_model
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (Δ : QWeilDivisor Y.scheme) (hΔ : 0 ≤ Δ)
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
    : Nonempty (multiplierModuleSheaf Y Δ ≅
      (SheafOfModules.pushforward π.toRingCatSheafHom).obj
        (divisorModuleSheaf (ceilQWeilDivisor (rationalWeilDivisor KW - Q))))
 := by
  let f := multiplierToRoundup Y Δ W hW π hbir hπ KW hKW Q hQ
  have hf : IsIso f := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    exact multiplierToRoundupApp_bijective Y hY Δ hΔ W hW π hbir hπ KW hKW Q hQ
      D hD c hSNC U
  let := hf
  exact ⟨asIso f⟩
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat

namespace NumericalDimensionOne
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y]

lemma divisorSectionOn_pullback (f : X ⟶ Y) [IsDominant f]
    {D : WeilDivisor Y} {P : WeilDivisor X} (hP : IsCartierPullback f D P)
    {U : Y.Opens} {r : Y.functionField} (hr : IsDivisorSectionOn D U r) :
    IsDivisorSectionOn P (f ⁻¹ᵁ U) (dominantFunctionFieldMap f r) := by
  by_cases hr0 : r = 0
  · exact Or.inl (by simp [hr0])
  right
  intro p hp
  obtain ⟨V,hV,hpV,g,hg,hDg,hPg⟩ := hP p.1
  obtain ⟨A,hA,hpA,hAVU⟩ := exists_isAffineOpen_mem_and_subset
    (show f p.1 ∈ V ⊓ U from ⟨hpV,hp⟩)
  let : Nonempty A := ⟨⟨f p.1,hpA⟩⟩
  obtain ⟨a,ha⟩ := (cartier_local_section_iff hA hg
    (fun q hq => hDg q (hAVU hq).1) r).mp
      (divisorSectionOn_res (le_trans hAVU inf_le_right) hr)
  have hreg : 0 ≤ X.ord (dominantFunctionFieldMap f (r*g)) p.1 := by
    apply (ord_nonnegative_iff_regular p _ ((map_ne_zero _).mpr (mul_ne_zero hr0 hg))).mpr
    refine ⟨f.stalkMap p.1 (Y.presheaf.germ A (f p.1) hpA a),?_⟩
    rw [← dominantFunctionFieldMap_algebraMap, Y.algebraMap_germ_eq_germToFunctionField,ha]
  rw [map_mul,X.ord_mul ((map_ne_zero _).mpr hr0) ((map_ne_zero _).mpr hg)] at hreg
  rwa [hPg p hpV]

omit [StalkwiseNormal X] in
lemma divisorSectionOn_mul [StalkwiseNormal X] {D E : WeilDivisor X} {U : X.Opens}
    {r s : X.functionField} (hr : IsDivisorSectionOn D U r)
    (hs : IsDivisorSectionOn E U s) : IsDivisorSectionOn (D+E) U (r*s) := by
  by_cases hr0 : r = 0
  · exact Or.inl (by simp [hr0])
  by_cases hs0 : s = 0
  · exact Or.inl (by simp [hs0])
  right
  intro p hp
  have h1 := hr.resolve_left hr0 p hp
  have h2 := hs.resolve_left hs0 p hp
  rw [X.ord_mul hr0 hs0,Finsupp.add_apply]
  omega

lemma divisorFunctionLocal_pullback (f : X ⟶ Y) [IsDominant f]
    {D : WeilDivisor Y} {P : WeilDivisor X} (hP : IsCartierPullback f D P)
    {U : Y.Opens} (s : divisorFunctionSubmodule D U) :
    (divisorFunctionLocal P).pred
      (fun x : f ⁻¹ᵁ U => dominantFunctionFieldMap f (s.1 ⟨f x.1,x.2⟩)) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    obtain ⟨r,hr,hsec⟩ := (divisorFunctionLocal_iff s.1).mp s.2
    apply PrelocalPredicate.sheafifyOf
    exact ⟨dominantFunctionFieldMap f r,
      fun x => congrArg (dominantFunctionFieldMap f) (hr ⟨f x.1,x.2⟩),
      divisorSectionOn_pullback f hP hsec⟩
  · have he : (fun x : f ⁻¹ᵁ U => dominantFunctionFieldMap f (s.1 ⟨f x.1,x.2⟩)) = 0 := by
      funext x
      exact (hU ⟨⟨f x.1,x.2⟩⟩).elim
    rw [he]
    exact divisorFunctionLocal_zero _ _

lemma divisorFunctionLocal_mul {D E : WeilDivisor X} {U : X.Opens}
    (s : divisorFunctionSubmodule D U) (t : divisorFunctionSubmodule E U) :
    (divisorFunctionLocal (D+E)).pred (fun x => s.1 x * t.1 x) := by
  classical
  by_cases hU : Nonempty U
  · let := hU
    obtain ⟨r,hr,hs⟩ := (divisorFunctionLocal_iff s.1).mp s.2
    obtain ⟨q,hq,ht⟩ := (divisorFunctionLocal_iff t.1).mp t.2
    apply PrelocalPredicate.sheafifyOf
    exact ⟨r*q,fun x => by dsimp only; rw [hr,hq],divisorSectionOn_mul hs ht⟩
  · have he : (fun x => s.1 x * t.1 x) = 0 := by
      funext x
      exact (hU ⟨x⟩).elim
    rw [he]
    exact divisorFunctionLocal_zero _ _

lemma cartier_open_section_iff {D : WeilDivisor X} {U : X.Opens} [Nonempty U]
    {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1)
    (r : X.functionField) :
    IsDivisorSectionOn D U r ↔ ∃ a : Γ(X,U), X.germToFunctionField U a = r*g := by
  rw [open_regular_iff_nonnegative_orders U]
  by_cases hr : r = 0
  · simp [IsDivisorSectionOn,hr]
  simp only [IsDivisorSectionOn,hr,false_or,mul_ne_zero hr hg,X.ord_mul hr hg]
  constructor <;> intro h p hp
  · simpa only [heq p hp] using h p hp
  · simpa only [heq p hp] using h p hp

noncomputable def cartierOpenChartMap {D : WeilDivisor X} {U : X.Opens}
    [Nonempty U] {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    Γ(X,U) →ₗ[Γ(X,U)] divisorFunctionSubmodule D U where
  toFun a := ⟨fun _ => X.germToFunctionField U a / g,
    (divisorFunctionLocal_iff _).mpr
      ⟨X.germToFunctionField U a/g,fun _ => rfl,
        (cartier_open_section_iff hg heq _).mpr ⟨a,(div_mul_cancel₀ _ hg).symm⟩⟩⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    funext x
    change X.germToFunctionField U (a+b)/g =
      X.germToFunctionField U a/g + X.germToFunctionField U b/g
    rw [map_add,add_div]
  map_smul' := by
    intro a b
    apply Subtype.ext
    funext x
    change X.germToFunctionField U (a*b)/g =
      regularFunctionValues U a x * (X.germToFunctionField U b/g)
    rw [regularFunctionValues_eq,map_mul,mul_div_assoc]

lemma cartierOpenChartMap_bijective {D : WeilDivisor X} {U : X.Opens}
    [Nonempty U] {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    Function.Bijective (cartierOpenChartMap hg heq) := by
  constructor
  · intro a b h
    have he := congrArg (fun s => s.1 (Classical.arbitrary U)) h
    change X.germToFunctionField U a/g = X.germToFunctionField U b/g at he
    apply X.germToFunctionField_injective U
    exact (div_left_inj' hg).mp he
  · intro s
    obtain ⟨r,hr,hs⟩ := (divisorFunctionLocal_iff s.1).mp s.2
    obtain ⟨a,ha⟩ := (cartier_open_section_iff hg heq r).mp hs
    refine ⟨a,?_⟩
    apply Subtype.ext
    funext x
    change X.germToFunctionField U a/g = s.1 x
    rw [ha,mul_div_cancel_right₀ r hg,hr]

noncomputable def cartierOpenChartEquiv {D : WeilDivisor X} {U : X.Opens}
    [Nonempty U] {g : X.functionField} (hg : g ≠ 0)
    (heq : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1) :
    Γ(X,U) ≃ₗ[Γ(X,U)] divisorFunctionSubmodule D U :=
  LinearEquiv.ofBijective (cartierOpenChartMap hg heq) (cartierOpenChartMap_bijective hg heq)
end NumericalDimensionOne

end OAI
