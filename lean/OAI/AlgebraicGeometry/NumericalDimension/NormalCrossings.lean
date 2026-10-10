import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.DifferentialDivisibility
import OAI.AlgebraicGeometry.NumericalDimension.KltMembers

namespace OAI

/-! Normal Crossings. -/

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

lemma topDifferentialMap_coefficient_pullback
    (k A B C F : Type*) [CommRing k] [CommRing A] [CommRing B] [CommRing C] [CommRing F]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k F]
    [Algebra A B] [Algebra A C] [Algebra A F] [Algebra B F] [Algebra C F]
    [IsScalarTower k A B] [IsScalarTower k A C] [IsScalarTower k A F]
    [IsScalarTower k B F] [IsScalarTower k C F]
    [IsScalarTower A B F] [IsScalarTower A C F]
    (n : ℕ) (ω : ⋀[B]^n Ω[B⁄k]) (u : ⋀[A]^n Ω[A⁄k])
    (v : ⋀[C]^n Ω[C⁄k]) (a : B) (c : C)
    (hω : ω = a • topDifferentialMap k A B n u)
    (hv : topDifferentialMap k A C n u = c • v) :
    topDifferentialMap k B F n ω =
      (algebraMap B F a * algebraMap C F c) • topDifferentialMap k C F n v := by
  rw [hω, map_smul, ← IsScalarTower.algebraMap_smul F a]
  have h₁ := LinearMap.congr_fun (topDifferentialMap_comp k A B F n) u
  have h₂ := LinearMap.congr_fun (topDifferentialMap_comp k A C F n) u
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h₁ h₂
  rw [h₁, ← h₂, hv, map_smul, ← IsScalarTower.algebraMap_smul F c, ← mul_smul]

lemma canonical_germ_generator
    (Y : Scheme) [IsIntegral Y] [IsLocallyNoetherian Y]
    (sY : Y ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n sY]
    (ω : rationalTopForms (.of ℂ) sY n) (D : WeilDivisor Y)
    (hD : IsCanonicalDivisorOf (.of ℂ) sY n ω D) (y : Y) :
    letI := schemeStalkAlgebra (.of ℂ) sY y
    letI := schemeFieldAlgebra (.of ℂ) sY
    letI := stalk_field_scalar_tower (.of ℂ) sY y
    ∃ (U : Y.Opens) (_ : y ∈ U) (a : Y.functionField)
      (v : ⋀[Y.presheaf.stalk y]^n Ω[(Y.presheaf.stalk y)⁄ℂ]),
      a ≠ 0 ∧ ω = a • topDifferentialMap ℂ (Y.presheaf.stalk y) Y.functionField n v ∧
      ∀ p : PrimeDivisor Y, p.1 ∈ U → D p = Y.ord a p.1 := by
  classical
  let := schemeStalkAlgebra (.of ℂ) sY y
  let := schemeFieldAlgebra (.of ℂ) sY
  let := stalk_field_scalar_tower (.of ℂ) sY y
  obtain ⟨U, hU, hyU, hs⟩ := exists_standard_smooth_chart sY n y
  let : Nonempty U := ⟨⟨y,hyU⟩⟩
  let := schemeOpenAlgebra sY U
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(Y,U) := hs
  let : Algebra.IsStandardSmooth ℂ Γ(Y,U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := open_field_scalar_tower sY U
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  let : Algebra.FormallyEtale Γ(Y,U) Y.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(Y,U))
  obtain ⟨bU⟩ := nonempty_topDifferential_basis ℂ Γ(Y,U) n
  let bF := (topDifferential_isBaseChange ℂ Γ(Y,U) Y.functionField n).basis bU
  let a := bF.repr ω 0
  have heq : ω = a • topDifferentialMap ℂ Γ(Y,U) Y.functionField n (bU 0) := by
    simpa only [bF, IsBaseChange.basis_apply] using basis_singleton_repr bF ω
  have ha : a ≠ 0 := by
    intro h
    exact hD.1 (by simpa [h] using heq)
  let u : U := ⟨y,hyU⟩
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf u
  let := open_stalk_scalar_tower sY U u
  let := functionField_isScalarTower Y U u
  refine ⟨U,hyU,a,topDifferentialMap ℂ Γ(Y,U) (Y.presheaf.stalk y) n (bU 0),ha,?_,
    canonical_chart_equation sY n hD U hU hs bU a ha heq⟩
  exact heq.trans (congrArg (fun v => a • v)
    (LinearMap.congr_fun (topDifferentialMap_comp ℂ Γ(Y,U)
      (Y.presheaf.stalk y) Y.functionField n) (bU 0)).symm)

lemma canonical_ramification_coefficient
    (X Y : Scheme) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] [SmoothOfRelativeDimension n sY]
    (f : X ⟶ Y) [IsDominant f] (hf : f ≫ sY = sX)
    (ω : rationalTopForms (.of ℂ) sY n)
    (DX : WeilDivisor X) (DY : WeilDivisor Y)
    (hDX : IsCanonicalDivisorOf (.of ℂ) sX n
      (rationalTopFormPullback (.of ℂ) sX sY f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) sY n ω DY)
    (P : WeilDivisor X) (hP : IsCartierPullback f DY P) (p : PrimeDivisor X) :
    letI := schemeStalkAlgebra (.of ℂ) sY (f p.1)
    letI := schemeStalkAlgebra (.of ℂ) sX p.1
    letI : Algebra (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
      (f.stalkMap p.1).hom.toAlgebra
    letI : IsScalarTower ℂ (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
      IsScalarTower.of_algebraMap_eq (fun z => (dominant_stalk_scalar (.of ℂ) sX sY f hf p.1 z).symm)
    ∃ (v : ⋀[Y.presheaf.stalk (f p.1)]^n Ω[(Y.presheaf.stalk (f p.1))⁄ℂ])
      (b : Module.Basis (Fin 1) (X.presheaf.stalk p.1)
        (⋀[X.presheaf.stalk p.1]^n Ω[(X.presheaf.stalk p.1)⁄ℂ]))
      (c : X.presheaf.stalk p.1),
      topDifferentialMap ℂ (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) n v = c • b 0 ∧
      algebraMap (X.presheaf.stalk p.1) X.functionField c ≠ 0 ∧
      DX p - P p = X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField c) p.1
 := by
  classical
  let := schemeStalkAlgebra (.of ℂ) sY (f p.1)
  let := schemeFieldAlgebra (.of ℂ) sX
  let := schemeFieldAlgebra (.of ℂ) sY
  let := stalk_field_scalar_tower (.of ℂ) sY (f p.1)
  let : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  let : IsScalarTower ℂ Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar (.of ℂ) sX sY f hf a).symm)
  obtain ⟨U, hpU, a, v, ha, heq, hDa⟩ := canonical_germ_generator Y sY n ω DY hDY (f p.1)
  have hPa := hP.order_eq_of_equation ha hDa p hpU
  let := schemeStalkAlgebra (.of ℂ) sX p.1
  let := stalk_field_scalar_tower (.of ℂ) sX p.1
  let : Algebra (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
    (f.stalkMap p.1).hom.toAlgebra
  let : IsScalarTower ℂ (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
    IsScalarTower.of_algebraMap_eq (fun z => (dominant_stalk_scalar (.of ℂ) sX sY f hf p.1 z).symm)
  let : Algebra (Y.presheaf.stalk (f p.1)) X.functionField :=
    ((dominantFunctionFieldMap f).comp (algebraMap (Y.presheaf.stalk (f p.1)) Y.functionField)).toAlgebra
  let : IsScalarTower (Y.presheaf.stalk (f p.1)) Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower ℂ (Y.presheaf.stalk (f p.1)) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap ℂ X.functionField z = dominantFunctionFieldMap f
      (algebraMap (Y.presheaf.stalk (f p.1)) Y.functionField
        (algebraMap ℂ (Y.presheaf.stalk (f p.1)) z))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominantFunctionFieldMap_scalar (.of ℂ) sX sY f hf z).symm
  let : IsScalarTower (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun z => dominantFunctionFieldMap_algebraMap f p.1 z)
  obtain ⟨bp⟩ := nonempty_smooth_canonical_stalk_basis sX n p.1
  let c := bp.repr (topDifferentialMap ℂ (Y.presheaf.stalk (f p.1))
    (X.presheaf.stalk p.1) n v) 0
  have hc : topDifferentialMap ℂ (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) n v =
      c • bp 0 := basis_singleton_repr bp _
  let cf := algebraMap (X.presheaf.stalk p.1) X.functionField c
  have hpull : rationalTopFormPullback (.of ℂ) sX sY f hf n ω =
      (dominantFunctionFieldMap f a * cf) •
        topDifferentialMap ℂ (X.presheaf.stalk p.1) X.functionField n (bp 0) := by
    change topDifferentialMap ℂ Y.functionField X.functionField n ω = _
    exact topDifferentialMap_coefficient_pullback ℂ (Y.presheaf.stalk (f p.1)) Y.functionField
      (X.presheaf.stalk p.1) X.functionField n ω v (bp 0) a c heq hc
  have hprod : dominantFunctionFieldMap f a * cf ≠ 0 := by
    intro h
    exact hDX.1 (by simpa [h] using hpull)
  have hcf : cf ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  obtain ⟨cp, a', ha', heq', hDXp⟩ := hDX.2 p
  have hDXord := canonical_local_order_unique sX n p _ cp bp a'
    (dominantFunctionFieldMap f a * cf) hDX.1 ha' hprod heq' hpull
  refine ⟨v, bp, c, hc, hcf, ?_⟩
  change DX p - P p = X.ord cf p.1
  rw [hDXp, hDXord, X.ord_mul ((map_ne_zero _).mpr ha) hcf, hPa]
  omega

theorem independent_boundary_discrepancy_bound_scheme
    (X Y : Scheme) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] [SmoothOfRelativeDimension n sY]
    (f : X ⟶ Y) [IsDominant f]
    (hf : f ≫ sY = sX)
    (ω : rationalTopForms (.of ℂ) sY n)
    (DX : WeilDivisor X) (DY : WeilDivisor Y)
    (hDX : IsCanonicalDivisorOf (.of ℂ) sX n
      (rationalTopFormPullback (.of ℂ) sX sY f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) sY n ω DY)
    (P : WeilDivisor X) (hP : IsCartierPullback f DY P)
    {ι : Type*} [Fintype ι]
    (D : ι → WeilDivisor Y) (T : ι → WeilDivisor X)
    (hT : ∀ i, IsCartierPullback f (D i) (T i)) (p : PrimeDivisor X) :
    letI := schemeStalkAlgebra (.of ℂ) sY (f p.1)
    ∀ (g : ∀ i, CartierStalkEquation (D i) (f p.1))
      (b : Module.Basis (Fin n) (Y.presheaf.stalk (f p.1))
        Ω[(Y.presheaf.stalk (f p.1))⁄ℂ]) (σ : ι ↪ Fin n),
      (∀ i, KaehlerDifferential.D ℂ (Y.presheaf.stalk (f p.1))
        (g i).regular = b (σ i)) →
      (∑ i, T i p) ≤ (DX - P) p + 1 := by
  classical
  let := schemeStalkAlgebra (.of ℂ) sY (f p.1)
  intro g bY σ hg
  let := schemeStalkAlgebra (.of ℂ) sX p.1
  let : Algebra (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
    (f.stalkMap p.1).hom.toAlgebra
  let : IsScalarTower ℂ (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) :=
    IsScalarTower.of_algebraMap_eq (fun z => (dominant_stalk_scalar (.of ℂ) sX sY f hf p.1 z).symm)
  obtain ⟨v, bp, c, hc, hcf, hDiff⟩ := canonical_ramification_coefficient
    X Y sX sY n f hf ω DX DY hDX hDY P hP p
  let cf := algebraMap (X.presheaf.stalk p.1) X.functionField c
  let gX (i : ι) := f.stalkMap p.1 (g i).regular
  have hgX (i : ι) :
      algebraMap (X.presheaf.stalk p.1) X.functionField (gX i) =
        dominantFunctionFieldMap f (g i).function := by
    rw [← (g i).regular_eq, dominantFunctionFieldMap_algebraMap]
  have hTord (i : ι) := (hT i).order_eq_of_equation (g i).nonzero
    (g i).equation p (g i).mem_openSet
  have hgXnz (i : ι) : gX i ≠ 0 := by
    intro hz
    have hgn : dominantFunctionFieldMap f (g i).function ≠ 0 := (map_ne_zero _).mpr (g i).nonzero
    apply hgn
    rw [← hgX i, hz, map_zero]
  let : IsDiscreteValuationRing (X.presheaf.stalk p.1) := dvr_at_prime_divisor p
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p.1)
  have hdecomp (i : ι) := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hgXnz i) ht
  choose e uu he using hdecomp
  obtain ⟨w, hw⟩ := topDifferentialMap_divisible_of_independent_equations bY σ
    (fun i => (g i).regular) t (fun i => ↑(uu i)) e hg he
    v
  have hcg : c = t ^ ((∑ i, e i) - 1) * (bp.repr w 0) := by
    have hz := congrArg (fun z => bp.repr z 0) (hc.symm.trans hw)
    simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] using hz
  have hTe (i : ι) : T i p = (e i : ℤ) := by
    rw [hTord i, ← hgX i, he i]
    exact order_stalk_unit_mul_pow p t ht (uu i) (e i)
  have hsum_T : (∑ i, T i p) = ((∑ i, e i) : ℕ) := by
    simp only [hTe, Nat.cast_sum]
  have hbound : (∑ i, T i p) ≤ X.ord cf p.1 + 1 := by
    rw [hsum_T]
    exact order_stalk_divisible_pow_lower_bound p t ht (∑ i, e i) c
      (bp.repr w 0) hcf hcg
  change (∑ i, T i p) ≤ DX p - P p + 1
  change (∑ i, T i p) ≤ X.ord cf p.1 + 1 at hbound
  change DX p - P p = X.ord cf p.1 at hDiff
  rwa [hDiff]

theorem independent_boundary_discrepancy_bound
    (X Y : ComplexProjectiveVariety) (n : ℕ)
    (hX : IsSmoothNfold X n) (hY : IsSmoothNfold Y n)
    [StalkwiseNormal Y.scheme]
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (ω : rationalTopForms (.of ℂ) Y.structureMap n)
    (DX : WeilDivisor X.scheme) (DY : WeilDivisor Y.scheme)
    (hDX : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) Y.structureMap n ω DY)
    (P : WeilDivisor X.scheme) (hP : IsCartierPullback f DY P)
    {ι : Type*} [Fintype ι]
    (D : ι → WeilDivisor Y.scheme) (T : ι → WeilDivisor X.scheme)
    (hT : ∀ i, IsCartierPullback f (D i) (T i)) (p : PrimeDivisor X.scheme) :
    letI := schemeStalkAlgebra (.of ℂ) Y.structureMap (f p.1)
    ∀ (g : ∀ i, CartierStalkEquation (D i) (f p.1))
      (b : Module.Basis (Fin n) (Y.scheme.presheaf.stalk (f p.1))
        Ω[(Y.scheme.presheaf.stalk (f p.1))⁄ℂ]) (σ : ι ↪ Fin n),
      (∀ i, KaehlerDifferential.D ℂ (Y.scheme.presheaf.stalk (f p.1))
        (g i).regular = b (σ i)) →
      (∑ i, T i p) ≤ (DX - P) p + 1 := by
  let : SmoothOfRelativeDimension n X.structureMap := hX
  let : SmoothOfRelativeDimension n Y.structureMap := hY
  let : StalkwiseNormal X.scheme := smoothNormal X hX
  exact independent_boundary_discrepancy_bound_scheme X.scheme Y.scheme
    X.structureMap Y.structureMap n f hf ω DX DY hDX hDY P hP D T hT p

def IsSimpleNormalCrossingsDivisorFamily
    (Y : ComplexProjectiveVariety) (n : ℕ) [StalkwiseNormal Y.scheme]
    {ι : Type*} [Fintype ι] (D : ι → WeilDivisor Y.scheme) : Prop :=
  (∀ i, IsCartierDivisor (D i) ∧ 0 ≤ D i) ∧
  ∀ x : Y.scheme,
    letI := schemeStalkAlgebra (.of ℂ) Y.structureMap x
    ∃ (g : ∀ i, CartierStalkEquation (D i) x)
      (b : Module.Basis (Fin n) (Y.scheme.presheaf.stalk x) Ω[(Y.scheme.presheaf.stalk x)⁄ℂ])
      (S : Finset ι) (σ : S ↪ Fin n),
      (∀ i : S, KaehlerDifferential.D ℂ (Y.scheme.presheaf.stalk x) (g i.1).regular = b (σ i)) ∧
      (∀ i ∉ S, IsUnit (g i).regular)

theorem snc_boundary_discrepancy_bound
    (X Y : ComplexProjectiveVariety) (n : ℕ)
    (hX : IsSmoothNfold X n) (hY : IsSmoothNfold Y n)
    [StalkwiseNormal Y.scheme]
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (ω : rationalTopForms (.of ℂ) Y.structureMap n)
    (DX : WeilDivisor X.scheme) (DY : WeilDivisor Y.scheme)
    (hDX : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) Y.structureMap n ω DY)
    (P : WeilDivisor X.scheme) (hP : IsCartierPullback f DY P)
    {ι : Type*} [Fintype ι] (D : ι → WeilDivisor Y.scheme)
    (hD : IsSimpleNormalCrossingsDivisorFamily Y n D)
    (T : ι → WeilDivisor X.scheme) (hT : ∀ i, IsCartierPullback f (D i) (T i)) :
    ∀ p : PrimeDivisor X.scheme, (∑ i, T i p) ≤ (DX - P) p + 1 := by
  classical
  intro p
  let := schemeStalkAlgebra (.of ℂ) Y.structureMap (f p.1)
  obtain ⟨g, b, S, σ, hcoord, hunit⟩ := hD.2 (f p.1)
  have hactive := independent_boundary_discrepancy_bound X Y n hX hY f hf ω DX DY
    hDX hDY P hP (fun i : S => D i.1) (fun i : S => T i.1)
    (fun i => hT i.1) p (fun i => g i.1) b σ hcoord
  have hzero (i : ι) (hi : i ∉ S) : T i p = 0 := by
    have hTord := (hT i).order_eq_of_equation (g i).nonzero (g i).equation p (g i).mem_openSet
    rw [hTord, ← (g i).regular_eq, dominantFunctionFieldMap_algebraMap]
    exact order_stalk_unit p ((hunit i hi).map (f.stalkMap p.1).hom)
  have hsum : (∑ i : S, T i.1 p) = ∑ i, T i p := by
    rw [Finset.sum_coe_sort S (fun i => T i p)]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i hi)
  rwa [hsum] at hactive

lemma IsQCartierPullback.sum {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {f : X ⟶ Y} [IsDominant f] {ι : Type*} (S : Finset ι)
    {D : ι → QWeilDivisor Y} {P : ι → QWeilDivisor X}
    (hP : ∀ i ∈ S, IsQCartierPullback f (D i) (P i)) :
    IsQCartierPullback f (∑ i ∈ S, D i) (∑ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa [rationalWeilDivisor] using (isCartierPullback_zero f).rational (cartierDivisors (X := Y)).zero_mem
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (hP i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem snc_boundary_isKlt
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    {ι : Type*} [Fintype ι] (D : ι → WeilDivisor Y.scheme)
    (hD : IsSimpleNormalCrossingsDivisorFamily Y.toComplexProjectiveVariety n D)
    (c : ι → ℚ) (hc : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i < 1) :
    IsKltBoundary Y (∑ i, c i • rationalWeilDivisor (D i)) := by
  classical
  have hK := canonicalModel_isCartier Y hY
  have hid : IsQCartierPullback (𝟙 Y.scheme)
      (∑ i, c i • rationalWeilDivisor (D i))
      (∑ i, c i • rationalWeilDivisor (D i)) :=
    IsQCartierPullback.sum Finset.univ (fun i _ =>
      ((hD.1 i).1.pullback_id.rational (hD.1 i).1).smul (c i))
  have hKpull := hK.pullback_id.rational hK
  refine ⟨?_, (hKpull.add hid).isQCartier, ?_⟩
  · intro p
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hc i) (by
      change 0 ≤ (D i p : ℚ)
      exact_mod_cast (hD.1 i).2 p))
  intro W hW f hdom _hproper _hbir hf KW hKW Q hQ p
  let : IsDominant f := hdom
  let : StalkwiseNormal W.scheme := smoothNormal W hW
  obtain ⟨P, hP⟩ := exists_cartierPullback f Y.canonical hK
  have hex (i : ι) := exists_cartierPullback f (D i) (hD.1 i).1
  choose T hT using hex
  have hsumPull : IsQCartierPullback f
      (∑ i, c i • rationalWeilDivisor (D i)) (∑ i, c i • rationalWeilDivisor (T i)) :=
    IsQCartierPullback.sum Finset.univ (fun i _ => ((hT i).rational (hD.1 i).1).smul (c i))
  have he := hQ.unique ((hP.rational hK).add hsumPull)
  rw [he, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.finsetSum_apply]
  change (-1 : ℚ) < (KW p : ℚ) - ((P p : ℚ) + ∑ i, c i * (T i p : ℚ))
  have ha := smooth_relative_canonical_effective W Y.toComplexProjectiveVariety n hW hY
    f hf Y.form KW Y.canonical hKW Y.canonical_of_form P hP p
  have hb := snc_boundary_discrepancy_bound W Y.toComplexProjectiveVariety n hW hY
    f hf Y.form KW Y.canonical hKW Y.canonical_of_form P hP D hD T hT p
  have haQ : (0 : ℚ) ≤ (KW p : ℚ) - (P p : ℚ) := by exact_mod_cast ha
  have hbQ : (∑ i, (T i p : ℚ)) ≤ (KW p : ℚ) - (P p : ℚ) + 1 := by
    exact_mod_cast hb
  have hnonneg (i : ι) : 0 ≤ (T i p : ℚ) := by
    exact_mod_cast (hT i).nonneg (hD.1 i).2 p
  by_cases hzero : ∀ i, T i p = 0
  · simp only [hzero, Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]
    linarith
  · push Not at hzero
    obtain ⟨j, hj⟩ := hzero
    have hjpos : 0 < (T j p : ℚ) :=
      lt_of_le_of_ne (hnonneg j) (by exact_mod_cast Ne.symm hj)
    have hlt : (∑ i, c i * (T i p : ℚ)) < ∑ i, (T i p : ℚ) := by
      apply Finset.sum_lt_sum
      · intro i _
        nlinarith [hc1 i, hnonneg i]
      · exact ⟨j, Finset.mem_univ _, by nlinarith [hc1 j]⟩
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
def IsSimpleNormalCrossingsDivisorFamilyOver
    (Y : Scheme) [IsIntegral Y] [IsLocallyNoetherian Y] [StalkwiseNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    {ι : Type*} [Fintype ι] (D : ι → WeilDivisor Y) : Prop :=
  (∀ i, IsCartierDivisor (D i) ∧ 0 ≤ D i) ∧
  ∀ x : Y,
    letI := schemeStalkAlgebra (.of ℂ) sY x
    ∃ (g : ∀ i, CartierStalkEquation (D i) x)
      (b : Module.Basis (Fin n) (Y.presheaf.stalk x) Ω[(Y.presheaf.stalk x)⁄ℂ])
      (S : Finset ι) (σ : S ↪ Fin n),
      (∀ i : S, KaehlerDifferential.D ℂ (Y.presheaf.stalk x) (g i.1).regular = b (σ i)) ∧
      (∀ i ∉ S, IsUnit (g i).regular)

theorem snc_boundary_discrepancy_bound_scheme
    (X Y : Scheme) [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] [SmoothOfRelativeDimension n sY]
    (f : X ⟶ Y) [IsDominant f]
    (hf : f ≫ sY = sX)
    (ω : rationalTopForms (.of ℂ) sY n)
    (DX : WeilDivisor X) (DY : WeilDivisor Y)
    (hDX : IsCanonicalDivisorOf (.of ℂ) sX n
      (rationalTopFormPullback (.of ℂ) sX sY f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) sY n ω DY)
    (P : WeilDivisor X) (hP : IsCartierPullback f DY P)
    {ι : Type*} [Fintype ι] (D : ι → WeilDivisor Y)
    (hD : IsSimpleNormalCrossingsDivisorFamilyOver Y sY n D)
    (T : ι → WeilDivisor X) (hT : ∀ i, IsCartierPullback f (D i) (T i)) :
    ∀ p : PrimeDivisor X, (∑ i, T i p) ≤ (DX - P) p + 1 := by
  classical
  intro p
  let := schemeStalkAlgebra (.of ℂ) sY (f p.1)
  obtain ⟨g, b, S, σ, hcoord, hunit⟩ := hD.2 (f p.1)
  have hactive := independent_boundary_discrepancy_bound_scheme X Y sX sY n f hf ω DX DY
    hDX hDY P hP (fun i : S => D i.1) (fun i : S => T i.1)
    (fun i => hT i.1) p (fun i => g i.1) b σ hcoord
  have hzero (i : ι) (hi : i ∉ S) : T i p = 0 := by
    have hTord := (hT i).order_eq_of_equation (g i).nonzero (g i).equation p (g i).mem_openSet
    rw [hTord, ← (g i).regular_eq, dominantFunctionFieldMap_algebraMap]
    exact order_stalk_unit p ((hunit i hi).map (f.stalkMap p.1).hom)
  have hsum : (∑ i : S, T i.1 p) = ∑ i, T i p := by
    rw [Finset.sum_coe_sort S (fun i => T i p)]
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i hi)
  rwa [hsum] at hactive

lemma snc_fractional_discrepancy_bound_scheme
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
    (c : ι → ℚ) (hc1 : ∀ i, c i < 1)
    (Q : QWeilDivisor X)
    (hQ : IsQCartierPullback f (rationalWeilDivisor DY + ∑ i, c i • rationalWeilDivisor (D i)) Q)
    (p : PrimeDivisor X) :
    (-1 : ℚ) < (DX p : ℚ) - Q p := by
  classical
  have hK := isCartier_of_isCanonical sY n ⟨ω, hDY⟩
  obtain ⟨P, hP⟩ := exists_cartierPullback f DY hK
  have hex (i : ι) := exists_cartierPullback f (D i) (hD.1 i).1
  choose T hT using hex
  have hsumPull : IsQCartierPullback f
      (∑ i, c i • rationalWeilDivisor (D i)) (∑ i, c i • rationalWeilDivisor (T i)) :=
    IsQCartierPullback.sum Finset.univ (fun i _ => ((hT i).rational (hD.1 i).1).smul (c i))
  have he := hQ.unique ((hP.rational hK).add hsumPull)
  rw [he, Finsupp.add_apply, Finsupp.finsetSum_apply]
  change (-1 : ℚ) < (DX p : ℚ) - ((P p : ℚ) + ∑ i, c i * (T i p : ℚ))
  have ha : 0 ≤ DX p - P p := by
    obtain ⟨v, b, z, _, hn, hz⟩ := canonical_ramification_coefficient
      X Y sX sY n f hf ω DX DY hDX hDY P hP p
    rw [hz]
    exact (ord_nonnegative_iff_regular p _ hn).mpr ⟨z, rfl⟩
  have hb := snc_boundary_discrepancy_bound_scheme X Y sX sY n
    f hf ω DX DY hDX hDY P hP D hD T hT p
  have haQ : (0 : ℚ) ≤ (DX p : ℚ) - (P p : ℚ) := by exact_mod_cast ha
  have hbQ : (∑ i, (T i p : ℚ)) ≤ (DX p : ℚ) - (P p : ℚ) + 1 := by
    exact_mod_cast hb
  have hnonneg (i : ι) : 0 ≤ (T i p : ℚ) := by
    exact_mod_cast (hT i).nonneg (hD.1 i).2 p
  by_cases hzero : ∀ i, T i p = 0
  · simp only [hzero, Int.cast_zero, mul_zero, Finset.sum_const_zero, add_zero]
    linarith
  · push Not at hzero
    obtain ⟨j, hj⟩ := hzero
    have hjpos : 0 < (T j p : ℚ) :=
      lt_of_le_of_ne (hnonneg j) (by exact_mod_cast Ne.symm hj)
    have hlt : (∑ i, c i * (T i p : ℚ)) < ∑ i, (T i p : ℚ) := by
      apply Finset.sum_lt_sum
      · intro i _
        nlinarith [hc1 i, hnonneg i]
      · exact ⟨j, Finset.mem_univ _, by nlinarith [hc1 j]⟩
    linarith

end
end NumericalDimensionOne

end OAI
