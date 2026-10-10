import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CanonicalChains
import OAI.AlgebraicGeometry.NumericalDimension.DifferentialBaseChange

namespace OAI

/-! Terminal Models. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
theorem smooth_relative_canonical_strict
    (X Y : ComplexProjectiveVariety) (n : ℕ)
    (hX : IsSmoothNfold X n) (hY : IsSmoothNfold Y n)
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hb : IsBirationalMorphism f)
    (hf : f ≫ Y.structureMap = X.structureMap)
    (ω : rationalTopForms (.of ℂ) Y.structureMap n)
    (DX : WeilDivisor X.scheme) (DY : WeilDivisor Y.scheme)
    (hDX : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) Y.structureMap n ω DY)
    (P : WeilDivisor X.scheme) (hP : IsCartierPullback f DY P) :
    ∀ p : PrimeDivisor X.scheme, 1 < Order.coheight (f p.1) → 0 < (DX - P) p := by
  classical
  let : SmoothOfRelativeDimension n X.structureMap := hX
  let : SmoothOfRelativeDimension n Y.structureMap := hY
  let : StalkwiseNormal X.scheme := smoothNormal X hX
  let : StalkwiseNormal Y.scheme := smoothNormal Y hY
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let := schemeFieldAlgebra (.of ℂ) Y.structureMap
  let : Algebra Y.scheme.functionField X.scheme.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  let : IsScalarTower ℂ Y.scheme.functionField X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf a).symm)
  intro p hp
  change 0 < DX p - P p
  obtain ⟨U, hU, hpU, hs⟩ := exists_standard_smooth_chart Y.structureMap n (f p.1)
  let : Nonempty U := ⟨⟨f p.1, hpU⟩⟩
  let := schemeOpenAlgebra Y.structureMap U
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(Y.scheme, U) := hs
  let : Algebra.IsStandardSmooth ℂ Γ(Y.scheme, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := open_field_scalar_tower Y.structureMap U
  let := functionField_isFractionRing_of_isAffineOpen Y.scheme U hU
  let : Algebra.FormallyEtale Γ(Y.scheme, U) Y.scheme.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(Y.scheme, U))
  obtain ⟨bU⟩ := nonempty_topDifferential_basis ℂ Γ(Y.scheme, U) n
  let bF := (topDifferential_isBaseChange ℂ Γ(Y.scheme, U) Y.scheme.functionField n).basis bU
  let a := bF.repr ω 0
  have heq : ω = a • topDifferentialMap ℂ Γ(Y.scheme, U) Y.scheme.functionField n (bU 0) := by
    simpa only [bF, IsBaseChange.basis_apply] using basis_singleton_repr bF ω
  have ha : a ≠ 0 := by
    intro h
    exact hDY.1 (by simpa [h] using heq)
  have hDa := canonical_chart_equation Y.structureMap n hDY U hU hs bU a ha heq
  have hPa := hP.order_eq_of_equation ha hDa p hpU
  let := schemeStalkAlgebra (.of ℂ) X.structureMap p.1
  let := stalk_field_scalar_tower (.of ℂ) X.structureMap p.1
  let u : U := ⟨f p.1, hpU⟩
  let := schemeStalkAlgebra (.of ℂ) Y.structureMap (f p.1)
  let := TopCat.Presheaf.algebra_section_stalk Y.scheme.presheaf u
  let := open_stalk_scalar_tower Y.structureMap U u
  let : Algebra Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) :=
    ((f.stalkMap p.1).hom.comp (Y.scheme.presheaf.germ U (f p.1) hpU).hom).toAlgebra
  let : IsScalarTower ℂ Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change schemeStalkScalar (.of ℂ) X.structureMap p.1 z =
      f.stalkMap p.1 (algebraMap Γ(Y.scheme, U) (Y.scheme.presheaf.stalk (f p.1))
        (algebraMap ℂ Γ(Y.scheme, U) z))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominant_stalk_scalar (.of ℂ) X.structureMap Y.structureMap f hf p.1 z).symm
  let : Algebra Γ(Y.scheme, U) X.scheme.functionField :=
    ((dominantFunctionFieldMap f).comp (Y.scheme.germToFunctionField U).hom).toAlgebra
  let : IsScalarTower Γ(Y.scheme, U) Y.scheme.functionField X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    rfl
  let : IsScalarTower ℂ Γ(Y.scheme, U) X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap ℂ X.scheme.functionField z =
      dominantFunctionFieldMap f
        (algebraMap Γ(Y.scheme, U) Y.scheme.functionField (algebraMap ℂ Γ(Y.scheme, U) z))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf z).symm
  let : IsScalarTower Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change dominantFunctionFieldMap f (Y.scheme.germToFunctionField U z) =
      algebraMap (X.scheme.presheaf.stalk p.1) X.scheme.functionField
        (f.stalkMap p.1 (Y.scheme.presheaf.germ U (f p.1) hpU z))
    rw [← dominantFunctionFieldMap_algebraMap, Y.scheme.algebraMap_germ_eq_germToFunctionField]
  obtain ⟨bp⟩ := nonempty_smooth_canonical_stalk_basis X.structureMap n p.1
  let v := topDifferentialMap ℂ Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) n (bU 0)
  let c := bp.repr v 0
  have hc : v = c • bp 0 := basis_singleton_repr bp v
  dsimp only [v] at hc
  let cf := algebraMap (X.scheme.presheaf.stalk p.1) X.scheme.functionField c
  have hpull : rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω =
      (dominantFunctionFieldMap f a * cf) •
        topDifferentialMap ℂ (X.scheme.presheaf.stalk p.1) X.scheme.functionField n (bp 0) := by
    change topDifferentialMap ℂ Y.scheme.functionField X.scheme.functionField n ω = _
    rw [heq, map_smul, ← IsScalarTower.algebraMap_smul X.scheme.functionField a]
    have hcomp₁ := LinearMap.congr_fun (topDifferentialMap_comp ℂ Γ(Y.scheme, U)
      Y.scheme.functionField X.scheme.functionField n) (bU 0)
    have hcomp₂ := LinearMap.congr_fun (topDifferentialMap_comp ℂ Γ(Y.scheme, U)
      (X.scheme.presheaf.stalk p.1) X.scheme.functionField n) (bU 0)
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hcomp₁ hcomp₂
    change _ • _ = _
    rw [hcomp₁, ← hcomp₂, hc, map_smul,
      ← IsScalarTower.algebraMap_smul X.scheme.functionField c, ← mul_smul]
    rfl
  have hprod : dominantFunctionFieldMap f a * cf ≠ 0 := by
    intro h
    exact hDX.1 (by simpa [h] using hpull)
  have hcf : cf ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  obtain ⟨cp, a', ha', heq', hDXp⟩ := hDX.2 p
  have hDXord := canonical_local_order_unique X.structureMap n p _ cp bp a'
    (dominantFunctionFieldMap f a * cf) hDX.1 ha' hprod heq' hpull
  rw [hDXp, hDXord, X.scheme.ord_mul ((map_ne_zero _).mpr ha) hcf, hPa]
  have hcpos : 0 ≤ X.scheme.ord cf p.1 :=
    (ord_nonnegative_iff_regular p cf hcf).mpr ⟨c, rfl⟩
  suffices h : 0 < X.scheme.ord cf p.1 by omega
  by_contra hn
  have hz : X.scheme.ord cf p.1 = 0 := by omega
  have hi : 0 ≤ X.scheme.ord cf⁻¹ p.1 := by
    rw [order_inv cf hcf, hz]
    simp
  obtain ⟨d, hd⟩ := (ord_nonnegative_iff_regular p cf⁻¹ (inv_ne_zero hcf)).mp hi
  have hunit : IsUnit c := by
    apply IsUnit.of_mul_eq_one d
    apply IsFractionRing.injective (X.scheme.presheaf.stalk p.1) X.scheme.functionField
    rw [map_mul, hd, map_one]
    exact mul_inv_cancel₀ hcf
  obtain ⟨bA⟩ := nonempty_standardSmooth_differential_basis ℂ Γ(Y.scheme, U) n
  obtain ⟨bB⟩ := nonempty_smooth_stalk_differential_basis X.structureMap n p.1
  let : Algebra.FormallyUnramified Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) :=
    formallyUnramified_of_topDifferential_unit ℂ Γ(Y.scheme, U)
      (X.scheme.presheaf.stalk p.1) n bA bB bp (bU 0) hunit
  let : Algebra (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) :=
    (f.stalkMap p.1).hom.toAlgebra
  let : IsScalarTower Γ(Y.scheme, U) (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra.FormallyUnramified (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) :=
    Algebra.FormallyUnramified.of_restrictScalars Γ(Y.scheme, U)
      (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1)
  let : LocallyOfFiniteType (f ≫ Y.structureMap) := hf.symm ▸ inferInstance
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f Y.structureMap
  let : Algebra.EssFiniteType (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) :=
    LocallyOfFiniteType.stalkMap f p.1
  have hcod := birational_quasiFinite_stalk_coheight f hb p.1 inferInstance
  rw [hcod, p.2] at hp
  exact lt_irrefl _ hp
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem smooth_isTerminalModel {n : ℕ} (Y : CanonicalModel n)
    (hY : IsSmoothNfold Y.toComplexProjectiveVariety n) : IsTerminalModel Y := by
  let : StalkwiseNormal Y.scheme := Y.normal
  intro W hW f hdom _hbProper hbir hf KW hKW Q hQ p hp
  let : IsDominant f := hdom
  obtain ⟨P, hP⟩ := exists_cartierPullback f Y.canonical (canonicalModel_isCartier Y hY)
  rw [IsQCartierPullback.eq_integral hP hQ]
  have h := smooth_relative_canonical_strict W Y.toComplexProjectiveVariety n hW hY
    f hbir hf Y.form KW Y.canonical hKW Y.canonical_of_form P hP p hp
  change 0 < KW p - P p at h
  change (0 : ℚ) < (KW p : ℚ) - (P p : ℚ)
  exact_mod_cast h
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma canonical_coefficient_of_stalk_iso
    (X Y : ComplexProjectiveVariety) (n : ℕ) (hY : IsSmoothNfold Y n)
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (ω : rationalTopForms (.of ℂ) Y.structureMap n)
    (DX : WeilDivisor X.scheme) (DY : WeilDivisor Y.scheme)
    (hDX : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) Y.structureMap n ω DY)
    (p : PrimeDivisor X.scheme) [IsIso (f.stalkMap p.1)]
    (hp : Order.coheight (f p.1) = 1) : DX p = DY ⟨f p.1,hp⟩ := by
  let : SmoothOfRelativeDimension n Y.structureMap := hY
  let := schemeStalkAlgebra (.of ℂ) Y.structureMap (f p.1)
  let := schemeStalkAlgebra (.of ℂ) X.structureMap p.1
  let := schemeFieldAlgebra (.of ℂ) Y.structureMap
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let := stalk_field_scalar_tower (.of ℂ) Y.structureMap (f p.1)
  let := stalk_field_scalar_tower (.of ℂ) X.structureMap p.1
  let : Algebra Y.scheme.functionField X.scheme.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  let : IsScalarTower ℂ Y.scheme.functionField X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf a).symm)
  let : Algebra (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) :=
    (f.stalkMap p.1).hom.toAlgebra
  let : IsScalarTower ℂ (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominant_stalk_scalar (.of ℂ) X.structureMap Y.structureMap f hf p.1 a).symm)
  let : Algebra (Y.scheme.presheaf.stalk (f p.1)) X.scheme.functionField :=
    ((dominantFunctionFieldMap f).comp
      (algebraMap (Y.scheme.presheaf.stalk (f p.1)) Y.scheme.functionField)).toAlgebra
  let : IsScalarTower (Y.scheme.presheaf.stalk (f p.1))
      Y.scheme.functionField X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => dominantFunctionFieldMap_algebraMap f p.1 a)
  let : IsScalarTower ℂ (Y.scheme.presheaf.stalk (f p.1)) X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap ℂ X.scheme.functionField a =
      dominantFunctionFieldMap f
        (algebraMap (Y.scheme.presheaf.stalk (f p.1)) Y.scheme.functionField
          (algebraMap ℂ (Y.scheme.presheaf.stalk (f p.1)) a))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf a).symm
  let : Module.Free (Y.scheme.presheaf.stalk (f p.1))
      Ω[Y.scheme.presheaf.stalk (f p.1)⁄ℂ] :=
    smooth_stalk_differentials_free Y.structureMap n (f p.1)
  let e := AlgEquiv.ofBijective
    (Algebra.ofId (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1))
    (ConcreteCategory.bijective_of_isIso (f.stalkMap p.1))
  let : Algebra.FormallyEtale (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) := Algebra.FormallyEtale.of_equiv e
  obtain ⟨b,a,ha,hω,hDYp⟩ := hDY.2 ⟨f p.1,hp⟩
  let bp := (topDifferential_isBaseChange ℂ (Y.scheme.presheaf.stalk (f p.1))
    (X.scheme.presheaf.stalk p.1) n).basis b
  have hωp : rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω =
      dominantFunctionFieldMap f a • topDifferentialMap ℂ (X.scheme.presheaf.stalk p.1)
        X.scheme.functionField n (bp 0) := by
    change topDifferentialMap ℂ Y.scheme.functionField X.scheme.functionField n ω = _
    rw [hω,map_smul,← IsScalarTower.algebraMap_smul X.scheme.functionField a]
    rw [(topDifferential_isBaseChange ℂ (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) n).basis_apply]
    have h₁ := LinearMap.congr_fun (topDifferentialMap_comp ℂ
      (Y.scheme.presheaf.stalk (f p.1)) Y.scheme.functionField X.scheme.functionField n) (b 0)
    have h₂ := LinearMap.congr_fun (topDifferentialMap_comp ℂ
      (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1)
        X.scheme.functionField n) (b 0)
    exact congrArg (fun z => dominantFunctionFieldMap f a • z) (h₁.trans h₂.symm)
  obtain ⟨c,a',ha',hω',hDXp⟩ := hDX.2 p
  rw [hDXp,canonical_local_order_unique X.structureMap n p _ c bp a'
    (dominantFunctionFieldMap f a) hDX.1 ha' ((map_ne_zero _).mpr ha) hω' hωp,
    order_dominantFunctionFieldMap_of_stalk_iso f p hp a ha,hDYp]
lemma canonical_comparison_strict_source_primes {n : ℕ}
    (X Y : CanonicalModel n) (hX : IsSmoothNfold X.toComplexProjectiveVariety n)
    (hY : IsTerminalModel Y) (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    (p : W.scheme ⟶ X.scheme) (q : W.scheme ⟶ Y.scheme)
    [IsDominant p] [IsDominant q] [IsProper p] [IsProper q]
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hp : p ≫ X.structureMap = W.structureMap) (hq : q ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKp : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap X.structureMap p hp n X.form) KW)
    (hKq : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap q hq n Y.form) KW)
    (P Q : QWeilDivisor W.scheme)
    (hP : IsQCartierPullback p (rationalWeilDivisor X.canonical) P)
    (hQ : IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q)
    (F : PrimeDivisor W.scheme) (hFp : Order.coheight (p F.1) = 1)
    (hFq : 1 < Order.coheight (q F.1)) : 0 < (P - Q) F := by
  obtain ⟨G,_hG,hiso,hunique⟩ := exists_unique_prime_over_of_proper_birational
    p hpb ⟨p F.1,hFp⟩
  have hFG : F = G := Subtype.ext (hunique F.1 rfl)
  subst G
  let : IsIso (p.stalkMap F.1) := hiso
  have hKW := canonical_coefficient_of_stalk_iso W X.toComplexProjectiveVariety n hX
    p hp X.form KW X.canonical hKp X.canonical_of_form F hFp
  obtain ⟨A,hA⟩ := exists_cartierPullback p X.canonical (canonicalModel_isCartier X hX)
  have hPa := IsQCartierPullback.eq_integral hA hP
  have hPF : P F = (KW F : ℚ) := by
    rw [hPa]
    change (A F : ℚ) = (KW F : ℚ)
    exact congrArg (fun z : ℤ => (z : ℚ))
      ((hA.coeff_eq_of_stalk_iso p F hFp).trans hKW.symm)
  have ht := hY W hW q inferInstance inferInstance hqb hq KW hKq Q hQ F hFq
  change 0 < P F - Q F
  rw [hPF]
  exact ht
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open scoped TensorProduct
lemma Kaehler_free_of_algebraMap_bijective (k A B : Type*)
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Module.Free B Ω[B⁄k]] (he : Function.Bijective (algebraMap A B)) :
    Module.Free A Ω[A⁄k] := by
  let e := AlgEquiv.ofBijective (Algebra.ofId A B) he
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_equiv e
  let : Module.Free A B := Module.Free.of_equiv e.toLinearEquiv
  let : Module.Free A Ω[B⁄k] := Module.Free.trans (S := B)
  let h := KaehlerDifferential.isBaseChange_of_formallyEtale k A B
  let u := (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl A Ω[A⁄k])).trans
    (TensorProduct.lid A Ω[A⁄k])
  exact Module.Free.of_equiv ((h.equiv.restrictScalars A).symm.trans u)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma canonical_coefficient_of_smooth_source_stalk_iso
    (X Y : ComplexProjectiveVariety) (n : ℕ) (hX : IsSmoothNfold X n)
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (ω : rationalTopForms (.of ℂ) Y.structureMap n)
    (DX : WeilDivisor X.scheme) (DY : WeilDivisor Y.scheme)
    (hDX : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) Y.structureMap n ω DY)
    (p : PrimeDivisor X.scheme) [IsIso (f.stalkMap p.1)]
    (hp : Order.coheight (f p.1) = 1) : DX p = DY ⟨f p.1,hp⟩ := by
  let : SmoothOfRelativeDimension n X.structureMap := hX
  let := schemeStalkAlgebra (.of ℂ) Y.structureMap (f p.1)
  let := schemeStalkAlgebra (.of ℂ) X.structureMap p.1
  let := schemeFieldAlgebra (.of ℂ) Y.structureMap
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let := stalk_field_scalar_tower (.of ℂ) Y.structureMap (f p.1)
  let := stalk_field_scalar_tower (.of ℂ) X.structureMap p.1
  let : Algebra Y.scheme.functionField X.scheme.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  let : IsScalarTower ℂ Y.scheme.functionField X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf a).symm)
  let : Algebra (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) :=
    (f.stalkMap p.1).hom.toAlgebra
  let : IsScalarTower ℂ (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominant_stalk_scalar (.of ℂ) X.structureMap Y.structureMap f hf p.1 a).symm)
  let : Algebra (Y.scheme.presheaf.stalk (f p.1)) X.scheme.functionField :=
    ((dominantFunctionFieldMap f).comp
      (algebraMap (Y.scheme.presheaf.stalk (f p.1)) Y.scheme.functionField)).toAlgebra
  let : IsScalarTower (Y.scheme.presheaf.stalk (f p.1))
      Y.scheme.functionField X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a => dominantFunctionFieldMap_algebraMap f p.1 a)
  let : IsScalarTower ℂ (Y.scheme.presheaf.stalk (f p.1)) X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap ℂ X.scheme.functionField a =
      dominantFunctionFieldMap f
        (algebraMap (Y.scheme.presheaf.stalk (f p.1)) Y.scheme.functionField
          (algebraMap ℂ (Y.scheme.presheaf.stalk (f p.1)) a))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf a).symm
  let : Module.Free (X.scheme.presheaf.stalk p.1)
      Ω[X.scheme.presheaf.stalk p.1⁄ℂ] :=
    smooth_stalk_differentials_free X.structureMap n p.1
  let : Module.Free (Y.scheme.presheaf.stalk (f p.1))
      Ω[Y.scheme.presheaf.stalk (f p.1)⁄ℂ] :=
    Kaehler_free_of_algebraMap_bijective ℂ (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) (ConcreteCategory.bijective_of_isIso (f.stalkMap p.1))
  let e := AlgEquiv.ofBijective
    (Algebra.ofId (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1))
    (ConcreteCategory.bijective_of_isIso (f.stalkMap p.1))
  let : Algebra.FormallyEtale (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) := Algebra.FormallyEtale.of_equiv e
  obtain ⟨b,a,ha,hω,hDYp⟩ := hDY.2 ⟨f p.1,hp⟩
  let bp := (topDifferential_isBaseChange ℂ (Y.scheme.presheaf.stalk (f p.1))
    (X.scheme.presheaf.stalk p.1) n).basis b
  have hωp : rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω =
      dominantFunctionFieldMap f a • topDifferentialMap ℂ (X.scheme.presheaf.stalk p.1)
        X.scheme.functionField n (bp 0) := by
    change topDifferentialMap ℂ Y.scheme.functionField X.scheme.functionField n ω = _
    rw [hω,map_smul,← IsScalarTower.algebraMap_smul X.scheme.functionField a]
    rw [(topDifferential_isBaseChange ℂ (Y.scheme.presheaf.stalk (f p.1))
      (X.scheme.presheaf.stalk p.1) n).basis_apply]
    have h₁ := LinearMap.congr_fun (topDifferentialMap_comp ℂ
      (Y.scheme.presheaf.stalk (f p.1)) Y.scheme.functionField X.scheme.functionField n) (b 0)
    have h₂ := LinearMap.congr_fun (topDifferentialMap_comp ℂ
      (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1)
        X.scheme.functionField n) (b 0)
    exact congrArg (fun z => dominantFunctionFieldMap f a • z) (h₁.trans h₂.symm)
  obtain ⟨c,a',ha',hω',hDXp⟩ := hDX.2 p
  rw [hDXp,canonical_local_order_unique X.structureMap n p _ c bp a'
    (dominantFunctionFieldMap f a) hDX.1 ha' ((map_ne_zero _).mpr ha) hω' hωp,
    order_dominantFunctionFieldMap_of_stalk_iso f p hp a ha,hDYp]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma IsQCartierPullback.coeff_eq_of_stalk_iso
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsDominant f] (q : PrimeDivisor X)
    [IsIso (f.stalkMap q.1)] (hp : Order.coheight (f q.1) = 1)
    {D : QWeilDivisor Y} {P : QWeilDivisor X} (hP : IsQCartierPullback f D P) :
    P q = D ⟨f q.1,hp⟩ := by
  obtain ⟨m,hm,A,B,_hA,hD,hB,hAB⟩ := hP
  have hb := DFunLike.congr_fun hB q
  have hd := DFunLike.congr_fun hD ⟨f q.1,hp⟩
  change (m : ℚ) * P q = (B q : ℚ) at hb
  change (m : ℚ) * D ⟨f q.1,hp⟩ = (A ⟨f q.1,hp⟩ : ℚ) at hd
  apply mul_left_cancel₀ (show (m : ℚ) ≠ 0 by exact_mod_cast hm.ne')
  exact hb.trans ((congrArg (fun z : ℤ => (z : ℚ))
    (hAB.coeff_eq_of_stalk_iso f q hp)).trans hd.symm)
lemma relativeCanonical_vanishes_over_prime {n : ℕ}
    (Y : CanonicalModel n) (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    (q : W.scheme ⟶ Y.scheme) [IsDominant q] [IsProper q]
    (hqb : IsBirationalMorphism q) (hq : q ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKq : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap q hq n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q)
    (F : PrimeDivisor W.scheme) (hF : Order.coheight (q F.1) = 1) :
    (rationalWeilDivisor KW - Q) F = 0 := by
  obtain ⟨G,_hG,hiso,hunique⟩ := exists_unique_prime_over_of_proper_birational
    q hqb ⟨q F.1,hF⟩
  have hFG : F = G := Subtype.ext (hunique F.1 rfl)
  subst G
  let : IsIso (q.stalkMap F.1) := hiso
  have hKW := canonical_coefficient_of_smooth_source_stalk_iso W Y.toComplexProjectiveVariety
    n hW q hq Y.form KW Y.canonical hKq Y.canonical_of_form F hF
  have hQF := hQ.coeff_eq_of_stalk_iso q F hF
  change (KW F : ℚ) - Q F = 0
  rw [hQF]
  change (KW F : ℚ) - (Y.canonical ⟨q F.1,hF⟩ : ℚ) = 0
  rw [hKW,sub_self]
lemma relativeCanonical_effective_terminal {n : ℕ}
    (Y : CanonicalModel n) (hY : IsTerminalModel Y)
    (W : ComplexProjectiveVariety) (hW : IsSmoothNfold W n)
    (q : W.scheme ⟶ Y.scheme) [IsDominant q] [IsProper q]
    (hqb : IsBirationalMorphism q) (hq : q ≫ Y.structureMap = W.structureMap)
    (KW : WeilDivisor W.scheme)
    (hKq : IsCanonicalDivisorOf (.of ℂ) W.structureMap n
      (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap q hq n Y.form) KW)
    (Q : QWeilDivisor W.scheme)
    (hQ : IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q) :
    0 ≤ rationalWeilDivisor KW - Q ∧
      (∀ F : PrimeDivisor W.scheme, (rationalWeilDivisor KW - Q) F ≠ 0 ↔
        1 < Order.coheight (q F.1)) := by
  have hpos (F : PrimeDivisor W.scheme) : 0 < Order.coheight (q F.1) := by
    apply pos_iff_ne_zero.mpr
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
  have hone (F : PrimeDivisor W.scheme) : 1 ≤ Order.coheight (q F.1) :=
    Order.one_le_iff_ne_zero.mpr (ne_of_gt (hpos F))
  have hzero (F : PrimeDivisor W.scheme) (hF : Order.coheight (q F.1) = 1) :=
    relativeCanonical_vanishes_over_prime Y W hW q hqb hq KW hKq Q hQ F hF
  have hstrict (F : PrimeDivisor W.scheme) (hF : 1 < Order.coheight (q F.1)) :=
    hY W hW q inferInstance inferInstance hqb hq KW hKq Q hQ F hF
  constructor
  · intro F
    rcases (hone F).eq_or_lt with hF | hF
    · exact le_of_eq (hzero F hF.symm).symm
    · exact (hstrict F hF).le
  · intro F
    constructor
    · intro hn
      exact lt_of_le_of_ne (hone F) (fun he => hn (hzero F he.symm))
    · intro hF
      exact ne_of_gt (hstrict F hF)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open scoped TensorProduct
lemma topDifferentialMap_bijective_of_algebraMap_bijective (k A B : Type*)
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Module.Free A Ω[A⁄k]] (he : Function.Bijective (algebraMap A B)) (n : ℕ) :
    Function.Bijective (topDifferentialMap k A B n) := by
  let e := AlgEquiv.ofBijective (Algebra.ofId A B) he
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_equiv e
  let h := topDifferential_isBaseChange k A B n
  let u := (TensorProduct.congr e.symm.toLinearEquiv
    (LinearEquiv.refl A (⋀[A]^n Ω[A⁄k]))).trans (TensorProduct.lid A (⋀[A]^n Ω[A⁄k]))
  let v := u.symm.trans (h.equiv.restrictScalars A)
  have hu (x : ⋀[A]^n Ω[A⁄k]) : u (1 ⊗ₜ[A] x) = x := by
    simp [u]
  have hv (x : ⋀[A]^n Ω[A⁄k]) : v x = topDifferentialMap k A B n x := by
    show h.equiv (u.symm x) = _
    have hs : u.symm x = 1 ⊗ₜ[A] x := (u.symm_apply_eq).mpr (hu x).symm
    rw [hs,IsBaseChange.equiv_tmul,one_smul]
  exact (show (v : (⋀[A]^n Ω[A⁄k]) → (⋀[B]^n Ω[B⁄k])) =
    topDifferentialMap k A B n from funext hv) ▸ v.bijective
end NumericalDimensionOne

end OAI
