import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CanonicalExistence

namespace OAI

/-! Differential Base Change. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
section
variable {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
private lemma IsCartierPullback.nsmul_local {morphism : X ⟶ Y} [IsDominant morphism]
    {divisor : WeilDivisor Y} {pullback : WeilDivisor X}
    (pullback_spec : IsCartierPullback morphism divisor pullback) (multiple : ℕ) :
    IsCartierPullback morphism (multiple • divisor) (multiple • pullback) := by
  induction multiple with
  | zero => simpa using isCartierPullback_zero morphism
  | succ multiple induction_hypothesis =>
    simpa only [succ_nsmul] using induction_hypothesis.add pullback_spec

lemma IsCartierPullback.eq_ord_on_open [StalkwiseNormal Y]
    {f : X ⟶ Y} [IsDominant f] {D : WeilDivisor Y} {E : WeilDivisor X}
    (hE : IsCartierPullback f D E) {U : Y.Opens} {a : Y.functionField}
    (ha : a ≠ 0) (hDa : ∀ p : PrimeDivisor Y, p.1 ∈ U → D p = Y.ord a p.1)
    (p : PrimeDivisor X) (hp : f p.1 ∈ U) :
    E p = X.ord (dominantFunctionFieldMap f a) p.1 := by
  obtain ⟨V,_,hpV,b,hb,hDb,hEb⟩ := hE p.1
  rw [hEb p hpV]
  exact pulled_equation_order_eq f hb ha hDb hDa p hpV hp
lemma IsCartierPullback.comp [StalkwiseNormal Y]
    {f : X ⟶ Y} {g : Y ⟶ Z} [IsDominant f] [IsDominant g]
    {D : WeilDivisor Z} {E : WeilDivisor Y} {F : WeilDivisor X}
    (hg : IsCartierPullback g D E) (hf : IsCartierPullback f E F) :
    IsCartierPullback (f ≫ g) D F := by
  intro x
  obtain ⟨U,hU,hx,a,ha,hDa,hEa⟩ := hg (f x)
  refine ⟨U,hU,hx,a,ha,hDa,?_⟩
  intro p hp
  rw [dominantFunctionFieldMap_comp_apply]
  exact hf.eq_ord_on_open ((map_ne_zero _).mpr ha)
    (U := g ⁻¹ᵁ U) (fun q hq => hEa q hq) p hp
lemma IsQCartierPullback.comp [StalkwiseNormal Y]
    {f : X ⟶ Y} {g : Y ⟶ Z} [IsDominant f] [IsDominant g]
    {D : QWeilDivisor Z} {E : QWeilDivisor Y} {F : QWeilDivisor X}
    (hg : IsQCartierPullback g D E) (hf : IsQCartierPullback f E F) :
    IsQCartierPullback (f ≫ g) D F := by
  obtain ⟨m,hm,A,B,hA,hAD,hBE,hAB⟩ := hg
  obtain ⟨n,hn,C,G,_,hCE,hGF,hCG⟩ := hf
  have hBC : n • B = m • C := by
    ext p
    have hb := DFunLike.congr_fun hBE p
    have hc := DFunLike.congr_fun hCE p
    change (m : ℚ) * E p = (B p : ℚ) at hb
    change (n : ℚ) * E p = (C p : ℚ) at hc
    have he : (n : ℚ) * (B p : ℚ) = (m : ℚ) * (C p : ℚ) := by
      rw [← hb, ← hc]; ring
    change (n : ℤ) * B p = (m : ℤ) * C p
    exact_mod_cast he
  have hnf := hCG.nsmul_local m
  rw [← hBC] at hnf
  refine ⟨m*n,Nat.mul_pos hm hn,n • A,m • G,
    (cartierDivisors (X := Z)).nsmul_mem hA n,?_,?_,(hAB.nsmul_local n).comp hnf⟩
  · ext p
    have h := DFunLike.congr_fun hAD p
    change (m : ℚ) * D p = (A p : ℚ) at h
    change ((m*n : ℕ) : ℚ) * D p = ((n : ℤ) * A p : ℤ)
    push_cast
    rw [← h]
    ring
  · ext p
    have h := DFunLike.congr_fun hGF p
    change (n : ℚ) * F p = (G p : ℚ) at h
    change ((m*n : ℕ) : ℚ) * F p = ((m : ℤ) * G p : ℤ)
    push_cast
    rw [← h]
    ring
end
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
lemma IsCartierPullback.nonneg [StalkwiseNormal X] [StalkwiseNormal Y]
    {f : X ⟶ Y} [IsDominant f] {D : WeilDivisor Y} {E : WeilDivisor X}
    (hE : IsCartierPullback f D E) (hD : 0 ≤ D) : 0 ≤ E := by
  intro p
  obtain ⟨U,hU,hp,a,ha,hDa,hEa⟩ := hE p.1
  let : Nonempty U := ⟨⟨f p.1,hp⟩⟩
  obtain ⟨b,hb⟩ := (affine_regular_iff_nonnegative_orders hU a).mpr
    (Or.inr (fun q hq => (hDa q hq) ▸ hD q))
  rw [hEa p hp]
  apply (ord_nonnegative_iff_regular p _ ((map_ne_zero _).mpr ha)).mpr
  refine ⟨f.stalkMap p.1 (Y.presheaf.germ U (f p.1) hp b),?_⟩
  rw [← dominantFunctionFieldMap_algebraMap,
    Y.algebraMap_germ_eq_germToFunctionField hp,hb]
lemma IsQCartierPullback.isQCartier {f : X ⟶ Y} [IsDominant f]
    {D : QWeilDivisor Y} {E : QWeilDivisor X} (hE : IsQCartierPullback f D E) :
    IsQCartierDivisor E := by
  obtain ⟨m,hm,A,B,_,_,hB,hAB⟩ := hE
  exact ⟨m,hm,B,hAB.isCartier,hB⟩
lemma IsQCartierPullback.nonneg [StalkwiseNormal X] [StalkwiseNormal Y]
    {f : X ⟶ Y} [IsDominant f] {D : QWeilDivisor Y} {E : QWeilDivisor X}
    (hE : IsQCartierPullback f D E) (hD : 0 ≤ D) : 0 ≤ E := by
  obtain ⟨m,hm,A,B,_,hA,hB,hAB⟩ := hE
  have hApos : 0 ≤ A := by
    intro p
    have h := DFunLike.congr_fun hA p
    change (m : ℚ) * D p = (A p : ℚ) at h
    have hp : 0 ≤ (A p : ℚ) := h ▸ mul_nonneg (Nat.cast_nonneg m) (hD p)
    exact_mod_cast hp
  have hBpos := hAB.nonneg hApos
  intro p
  have h := DFunLike.congr_fun hB p
  change (m : ℚ) * E p = (B p : ℚ) at h
  have hp : 0 ≤ (B p : ℚ) := by exact_mod_cast hBpos p
  rw [← h] at hp
  exact nonneg_of_mul_nonneg_right hp (by exact_mod_cast hm)
lemma IsQCartierPullback.unique [StalkwiseNormal Y]
    {f : X ⟶ Y} [IsDominant f] {D : QWeilDivisor Y} {E F : QWeilDivisor X}
    (hE : IsQCartierPullback f D E) (hF : IsQCartierPullback f D F) : E = F := by
  obtain ⟨m,hm,A,B,_,hAD,hBE,hAB⟩ := hE
  obtain ⟨n,hn,C,G,_,hCD,hGF,hCG⟩ := hF
  have hAC : n • A = m • C := by
    ext p
    have ha := DFunLike.congr_fun hAD p
    have hc := DFunLike.congr_fun hCD p
    change (m : ℚ) * D p = (A p : ℚ) at ha
    change (n : ℚ) * D p = (C p : ℚ) at hc
    have he : (n : ℚ) * (A p : ℚ) = (m : ℚ) * (C p : ℚ) := by
      rw [← ha, ← hc]; ring
    change (n : ℤ) * A p = (m : ℤ) * C p
    exact_mod_cast he
  have hc := hCG.nsmul_local m
  rw [← hAC] at hc
  have hBG := (hAB.nsmul_local n).unique hc
  ext p
  have hb := DFunLike.congr_fun hBE p
  have hg := DFunLike.congr_fun hGF p
  have he := DFunLike.congr_fun hBG p
  change (m : ℚ) * E p = (B p : ℚ) at hb
  change (n : ℚ) * F p = (G p : ℚ) at hg
  change (n : ℤ) * B p = (m : ℤ) * G p at he
  have he' : (n : ℚ) * (B p : ℚ) = (m : ℚ) * (G p : ℚ) := by exact_mod_cast he
  apply mul_left_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)))
  calc
    (m : ℚ) * (n : ℚ) * E p = (n : ℚ) * (B p : ℚ) := by rw [← hb]; ring
    _ = (m : ℚ) * (G p : ℚ) := he'
    _ = (m : ℚ) * (n : ℚ) * F p := by rw [← hg]; ring
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
lemma IsCartierDivisor.pullback_id {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {D : WeilDivisor X} (hD : IsCartierDivisor D) : IsCartierPullback (𝟙 X) D D := by
  intro x
  obtain ⟨U,hU,hx,g,hg,he⟩ := hD x
  refine ⟨U,hU,hx,g,hg,he,?_⟩
  intro p hp
  rw [dominantFunctionFieldMap_id_apply]
  exact he p hp
lemma IsQCartierDivisor.pullback_id {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {D : QWeilDivisor X} (hD : IsQCartierDivisor D) : IsQCartierPullback (𝟙 X) D D := by
  obtain ⟨m,hm,A,hA,he⟩ := hD
  exact ⟨m,hm,A,A,hA,he,he,hA.pullback_id⟩
lemma HasEffectiveCanonicalComparison.refl {n : ℕ} (X : CanonicalModel n)
    (hX : IsSmoothNfold X.toComplexProjectiveVariety n) :
    HasEffectiveCanonicalComparison X X (.refl X.scheme) := by
  have hφ : (Scheme.PartialIso.refl X.scheme).IsOver (𝟙 X.scheme) (𝟙 X.scheme) :=
    Category.id_comp _
  refine ⟨X.toComplexProjectiveVariety,hX,𝟙 X.scheme,𝟙 X.scheme,
    inferInstance,inferInstance,inferInstance,inferInstance,Category.id_comp _,Category.id_comp _,
    .refl X.scheme,hφ,hφ.trans hφ,rationalWeilDivisor X.canonical,
    rationalWeilDivisor X.canonical,0,X.qCartier.pullback_id,X.qCartier.pullback_id,
    (add_zero _).symm,le_refl _,?_,?_⟩
  · intro F hF
    exact (hF rfl).elim
  · intro F hF hF'
    exact (not_lt_of_ge hF.le hF').elim
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

section CanonicalChartEquation
universe u
variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
  [IsLocallyNoetherian Y]

lemma canonical_chart_equation (sY : Y ⟶ Spec (.of k)) (n : ℕ)
    {ω : rationalTopForms (.of k) sY n} {D : WeilDivisor Y}
    (hD : IsCanonicalDivisorOf (.of k) sY n ω D)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := schemeOpenAlgebra sY U
    letI := schemeFieldAlgebra (.of k) sY
    letI := open_field_scalar_tower sY U
    ∀ (_ : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(Y, U))
      (bU : Module.Basis (Fin 1) Γ(Y, U) (⋀[Γ(Y, U)]^n Ω[Γ(Y, U)⁄k]))
      (a : Y.functionField), a ≠ 0 →
      ω = a • topDifferentialMap k Γ(Y, U) Y.functionField n (bU 0) →
      ∀ p : PrimeDivisor Y, p.1 ∈ U → D p = Y.ord a p.1 := by
  let := schemeOpenAlgebra sY U
  let := schemeFieldAlgebra (.of k) sY
  let := open_field_scalar_tower sY U
  intro hs bU a ha heq p hp
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(Y, U) := hs
  let : Algebra.IsStandardSmooth k Γ(Y, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := schemeStalkAlgebra (.of k) sY p.1
  let := stalk_field_scalar_tower (.of k) sY p.1
  let y : U := ⟨p.1, hp⟩
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf y
  let := open_stalk_scalar_tower sY U y
  let := functionField_isScalarTower Y U y
  let := hU.isLocalization_stalk y
  let : Algebra.FormallyEtale Γ(Y, U) (Y.presheaf.stalk p.1) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf y).asIdeal.primeCompl
  let bp := (topDifferential_isBaseChange k Γ(Y, U) (Y.presheaf.stalk p.1) n).basis bU
  have heqp : ω = a • topDifferentialMap k (Y.presheaf.stalk p.1) Y.functionField n (bp 0) := by
    rw [(topDifferential_isBaseChange k Γ(Y, U) (Y.presheaf.stalk p.1) n).basis_apply]
    exact heq.trans (congrArg (fun v => a • v)
      (LinearMap.congr_fun (topDifferentialMap_comp k Γ(Y, U)
        (Y.presheaf.stalk p.1) Y.functionField n) (bU 0)).symm)
  obtain ⟨cp, a', ha', hc, hDa'⟩ := hD.2 p
  rw [hDa']
  exact canonical_local_order_unique sY n p ω cp bp a' a hD.1 ha' ha hc heqp

end CanonicalChartEquation
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma dominant_stalk_scalar
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (k : CommRingCat) (sX : X ⟶ Spec k) (sY : Y ⟶ Spec k)
    (f : X ⟶ Y) [IsDominant f] (hf : f ≫ sY = sX) (x : X) (a : k) :
    f.stalkMap x (schemeStalkScalar k sY (f x) a) = schemeStalkScalar k sX x a := by
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [← dominantFunctionFieldMap_algebraMap]
  have hY := X.algebraMap_germ_eq_germToFunctionField (by trivial : x ∈ (⊤ : X.Opens))
    (sX.appTop ((Scheme.ΓSpecIso k).inv a))
  have hX := Y.algebraMap_germ_eq_germToFunctionField (by trivial : f x ∈ (⊤ : Y.Opens))
    (sY.appTop ((Scheme.ΓSpecIso k).inv a))
  change dominantFunctionFieldMap f
    (algebraMap (Y.presheaf.stalk (f x)) Y.functionField
      (Y.presheaf.germ ⊤ (f x) (by trivial) (sY.appTop ((Scheme.ΓSpecIso k).inv a)))) =
    algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ ⊤ x (by trivial) (sX.appTop ((Scheme.ΓSpecIso k).inv a)))
  rw [hX, hY]
  exact dominantFunctionFieldMap_scalar k sX sY f hf a
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem smooth_relative_canonical_effective
    (X Y : ComplexProjectiveVariety) (n : ℕ)
    (hX : IsSmoothNfold X n) (hY : IsSmoothNfold Y n)
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (ω : rationalTopForms (.of ℂ) Y.structureMap n)
    (DX : WeilDivisor X.scheme) (DY : WeilDivisor Y.scheme)
    (hDX : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) Y.structureMap n ω DY)
    (P : WeilDivisor X.scheme) (hP : IsCartierPullback f DY P) :
    0 ≤ DX - P := by
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
  intro p
  change 0 ≤ DX p - P p
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
  have hPa := hP.eq_ord_on_open ha hDa p hpU
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
  omega
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma exterior_volume_spans
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (b : Module.Basis (Fin n) R M) (x : ⋀[R]^n M) :
    ∃ c : R, x = c • exteriorPower.ιMulti R n b := by
  classical
  have h : (exteriorPower.ιMulti R n : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M)) =
      b.det.smulRight (exteriorPower.ιMulti R n b) := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change exteriorPower.ιMulti R n (b ∘ σ) =
      b.det.smulRight (exteriorPower.ιMulti R n b) (b ∘ σ)
    simp [AlternatingMap.map_perm, AlternatingMap.smulRight_apply, Module.Basis.det_self]
  have hx : x ∈ Submodule.span R {exteriorPower.ιMulti R n b} := by
    have hr : Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) ≤
        Submodule.span R {exteriorPower.ιMulti R n b} := by
      rw [Submodule.span_le]
      rintro _ ⟨v, rfl⟩
      rw [DFunLike.congr_fun h v]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    rw [exteriorPower.ιMulti_span] at hr
    exact hr (Submodule.mem_top)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨c, hc.symm⟩

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem formallyUnramified_of_topDifferential_unit
    (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (n : ℕ) (bA : Module.Basis (Fin n) A Ω[A⁄k])
    (bB : Module.Basis (Fin n) B Ω[B⁄k])
    (b : Module.Basis (Fin 1) B (⋀[B]^n Ω[B⁄k]))
    (z : ⋀[A]^n Ω[A⁄k])
    (hu : IsUnit (b.repr (topDifferentialMap k A B n z) 0)) :
    Algebra.FormallyUnramified A B := by
  classical
  let f := KaehlerDifferential.map k k A B
  let d := exteriorPower.alternatingMapLinearEquiv bB.det
  have hb : IsUnit (d (b 0)) := by
    have hr : exteriorPower.ιMulti B n bB =
        b.repr (exteriorPower.ιMulti B n bB) 0 • b 0 := by
      simpa using (b.sum_repr (exteriorPower.ιMulti B n bB)).symm
    have he := congrArg d hr
    have hprod : b.repr (exteriorPower.ιMulti B n bB) 0 * d (b 0) = 1 := by
      simpa only [d, map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
        Module.Basis.det_self, smul_eq_mul] using he.symm
    exact IsUnit.of_mul_eq_one _ (mul_comm _ _ |>.trans hprod)
  have hz : topDifferentialMap k A B n z =
      b.repr (topDifferentialMap k A B n z) 0 • b 0 := by
    simpa using (b.sum_repr (topDifferentialMap k A B n z)).symm
  have hdu : IsUnit (d (topDifferentialMap k A B n z)) := by
    rw [hz, map_smul, smul_eq_mul]
    exact hu.mul hb
  obtain ⟨a, rfl⟩ := exterior_volume_spans bA z
  have he : d (topDifferentialMap k A B n (a • exteriorPower.ιMulti A n bA)) =
      algebraMap A B a * bB.det (f ∘ bA) := by
    rw [map_smul, ← IsScalarTower.algebraMap_smul B a,
      topDifferentialMap_ιMulti, map_smul]
    simp only [d, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, smul_eq_mul]
    rfl
  rw [he] at hdu
  have hdet : IsUnit (bB.det (f ∘ bA)) := isUnit_of_mul_isUnit_right hdu
  have hspan := (bB.is_basis_iff_det.mpr hdet).2
  have hle : Submodule.span B (Set.range (f ∘ bA)) ≤
      LinearMap.range (KaehlerDifferential.mapBaseChange k A B) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨1 ⊗ₜ[A] bA i, by simp [f]⟩
  rw [hspan] at hle
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange k A B) :=
    LinearMap.range_eq_top.mp (top_le_iff.mp hle)
  constructor
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective k A B x
  exact (KaehlerDifferential.exact_mapBaseChange_map k A B y).mpr (hs y)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem nonempty_standardSmooth_differential_basis (k A : Type*)
    [CommRing k] [CommRing A] [Algebra k A] [Nontrivial A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n k A] :
    Nonempty (Module.Basis (Fin n) A Ω[A⁄k]) := by
  let : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have h : Module.finrank A Ω[A⁄k] = n :=
    Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  exact ⟨(Module.finBasis A Ω[A⁄k]).reindex (finCongr h)⟩

universe u

theorem nonempty_smooth_stalk_differential_basis
    {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n sX] (x : X) :
    letI := schemeStalkAlgebra (.of k) sX x
    Nonempty (Module.Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k]) := by
  let := schemeStalkAlgebra (.of k) sX x
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  let y : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨y⟩
  let := schemeOpenAlgebra sX U
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U) := hs
  let : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := open_stalk_scalar_tower sX U y
  let := hU.isLocalization_stalk y
  let : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf y).asIdeal.primeCompl
  obtain ⟨bU⟩ := nonempty_standardSmooth_differential_basis k Γ(X, U) n
  exact ⟨(KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, U)
    (X.presheaf.stalk x)).basis bU⟩
end NumericalDimensionOne

end OAI
