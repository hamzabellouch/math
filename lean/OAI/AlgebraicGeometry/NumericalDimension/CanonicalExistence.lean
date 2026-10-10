import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CanonicalForms

namespace OAI

/-! Canonical Existence. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalExistence
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [CompactSpace X]

theorem exists_canonicalDivisor_of_smooth (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] :
    ∃ D : WeilDivisor X, IsCanonicalDivisor (.of k) sX n D := by
  classical
  let := schemeFieldAlgebra (.of k) sX
  obtain ⟨U, hU, hηU, hs⟩ := exists_standard_smooth_chart sX n (genericPoint X)
  let : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  let := schemeOpenAlgebra sX U
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U) := hs
  let : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := open_field_scalar_tower sX U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra.FormallyEtale Γ(X, U) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(X, U))
  obtain ⟨bU⟩ := nonempty_topDifferential_basis k Γ(X, U) n
  let bF := (topDifferential_isBaseChange k Γ(X, U) X.functionField n).basis bU
  let ω := bF 0
  have hω : ω ≠ 0 := bF.ne_zero 0
  have hlocal : ∀ p : PrimeDivisor X,
      letI := schemeStalkAlgebra (.of k) sX p.1
      letI := stalk_field_scalar_tower (.of k) sX p.1
      ∃ b : Module.Basis (Fin 1) (X.presheaf.stalk p.1)
        (⋀[X.presheaf.stalk p.1]^n Ω[X.presheaf.stalk p.1⁄k]),
      ∃ a : X.functionField, a ≠ 0 ∧
        ω = a • topDifferentialMap k (X.presheaf.stalk p.1) X.functionField n (b 0) ∧
        (p.1 ∈ U → X.ord a p.1 = 0) := by
    intro p
    let := schemeStalkAlgebra (.of k) sX p.1
    let := stalk_field_scalar_tower (.of k) sX p.1
    by_cases hp : p.1 ∈ U
    · let y : U := ⟨p.1, hp⟩
      let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
      let := open_stalk_scalar_tower sX U y
      let := functionField_isScalarTower X U y
      let := hU.isLocalization_stalk y
      let : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk p.1) :=
        Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf y).asIdeal.primeCompl
      let bp := (topDifferential_isBaseChange k Γ(X, U) (X.presheaf.stalk p.1) n).basis bU
      refine ⟨bp, 1, one_ne_zero, ?_, fun _ => ?_⟩
      · rw [one_smul]
        change bF 0 = topDifferentialMap k (X.presheaf.stalk p.1) X.functionField n (bp 0)
        rw [(topDifferential_isBaseChange k Γ(X, U) (X.presheaf.stalk p.1) n).basis_apply,
          (topDifferential_isBaseChange k Γ(X, U) X.functionField n).basis_apply]
        exact (LinearMap.congr_fun (topDifferentialMap_comp k Γ(X, U)
          (X.presheaf.stalk p.1) X.functionField n) (bU 0)).symm
      · exact (X.ord_eq_iff p.2 one_ne_zero).mpr (by simp)
    · obtain ⟨bp⟩ := nonempty_smooth_canonical_stalk_basis sX n p.1
      let bFp := (canonical_stalk_field_isBaseChange sX n p.1).basis bp
      let a := bFp.repr ω 0
      have heq : ω = a • bFp 0 := basis_singleton_repr bFp ω
      have ha : a ≠ 0 := by
        intro h
        exact hω (by simpa [h] using heq)
      refine ⟨bp, a, ha, ?_, fun hp' => (hp hp').elim⟩
      exact heq.trans (congrArg (fun v => a • v)
        ((canonical_stalk_field_isBaseChange sX n p.1).basis_apply bp 0))
  choose b a ha heq hzero using hlocal
  have hproper : (U : Set X)ᶜ ≠ Set.univ := by
    intro h
    have hη : genericPoint X ∈ (U : Set X)ᶜ := by rw [h]; trivial
    exact hη hηU
  have hfin : (Function.support (fun p : PrimeDivisor X => X.ord (a p) p.1)).Finite := by
    apply (finite_primeDivisors_in_closed U.isOpen.isClosed_compl hproper).subset
    intro p hp hpU
    exact hp (hzero p hpU)
  let D : WeilDivisor X := Finsupp.ofSupportFinite (fun p => X.ord (a p) p.1) hfin
  refine ⟨D, ω, hω, ?_⟩
  intro p
  exact ⟨b p, a p, ha p, heq p, rfl⟩

end CanonicalExistence
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalUniquenessHelpers

lemma basis_singleton_coordinate_isUnit {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    (b c : Module.Basis (Fin 1) R M) : IsUnit (b.repr (c 0) 0) := by
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨c.repr (b 0) 0, ?_⟩
  have h := congrArg (fun v => b.repr v 0) (basis_singleton_repr c (b 0))
  simpa using h.symm

end CanonicalUniquenessHelpers
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalLocalOrder
universe u
variable {k : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X]

lemma canonical_local_order_unique (sX : X ⟶ Spec k) (n : ℕ) (p : PrimeDivisor X) :
    letI := schemeStalkAlgebra k sX p.1
    letI := schemeFieldAlgebra k sX
    letI := stalk_field_scalar_tower k sX p.1
    ∀ (ω : rationalTopForms k sX n)
      (b c : Module.Basis (Fin 1) (X.presheaf.stalk p.1)
        (⋀[X.presheaf.stalk p.1]^n Ω[X.presheaf.stalk p.1⁄k]))
      (a a' : X.functionField), ω ≠ 0 → a ≠ 0 → a' ≠ 0 →
      ω = a • topDifferentialMap k (X.presheaf.stalk p.1) X.functionField n (b 0) →
      ω = a' • topDifferentialMap k (X.presheaf.stalk p.1) X.functionField n (c 0) →
      X.ord a p.1 = X.ord a' p.1 := by
  let := schemeStalkAlgebra k sX p.1
  let := schemeFieldAlgebra k sX
  let := stalk_field_scalar_tower k sX p.1
  intro ω b c a a' hω _ ha' hb hc
  let u := b.repr (c 0) 0
  have hu : IsUnit u := basis_singleton_coordinate_isUnit b c
  have hcu : c 0 = u • b 0 := basis_singleton_repr b (c 0)
  let v := topDifferentialMap k (X.presheaf.stalk p.1) X.functionField n (b 0)
  have hv : v ≠ 0 := by
    intro h
    exact hω (by simpa [v, h] using hb)
  let uf := algebraMap (X.presheaf.stalk p.1) X.functionField u
  have ha : a = a' * uf := by
    apply smul_left_injective X.functionField hv
    change a • v = (a' * uf) • v
    calc
      a • v = ω := hb.symm
      _ = a' • topDifferentialMap k (X.presheaf.stalk p.1) X.functionField n (c 0) := hc
      _ = (a' * uf) • v := by
        rw [hcu, map_smul, ← IsScalarTower.algebraMap_smul X.functionField u, mul_smul]
  rw [ha, X.ord_mul ha' (hu.map (algebraMap _ _)).ne_zero,
    order_stalk_unit p hu, add_zero]

end CanonicalLocalOrder
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalUniqueness
universe u
variable {k : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X]

theorem canonicalDivisorOf_unique (sX : X ⟶ Spec k) (n : ℕ)
    {ω : rationalTopForms k sX n} {D E : WeilDivisor X}
    (hD : IsCanonicalDivisorOf k sX n ω D)
    (hE : IsCanonicalDivisorOf k sX n ω E) : D = E := by
  ext p
  obtain ⟨b, a, ha, hωa, hDa⟩ := hD.2 p
  obtain ⟨c, a', ha', hωa', hEa'⟩ := hE.2 p
  rw [hDa, hEa']
  exact canonical_local_order_unique sX n p ω b c a a' hD.1 ha ha' hωa hωa'

end CanonicalUniqueness
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne
section CanonicalCartierProof
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X]

theorem isCartier_of_isCanonical (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] {D : WeilDivisor X}
    (hD : IsCanonicalDivisor (.of k) sX n D) : IsCartierDivisor D := by
  classical
  obtain ⟨ω, hω, hD⟩ := hD
  let := schemeFieldAlgebra (.of k) sX
  intro x
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let := schemeOpenAlgebra sX U
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U) := hs
  let : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := open_field_scalar_tower sX U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : Algebra.FormallyEtale Γ(X, U) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(X, U))
  obtain ⟨bU⟩ := nonempty_topDifferential_basis k Γ(X, U) n
  let bF := (topDifferential_isBaseChange k Γ(X, U) X.functionField n).basis bU
  let a := bF.repr ω 0
  have heq : ω = a • bF 0 := basis_singleton_repr bF ω
  have ha : a ≠ 0 := by
    intro h
    exact hω (by simpa [h] using heq)
  refine ⟨U, hU, hxU, a, ha, ?_⟩
  intro p hp
  let := schemeStalkAlgebra (.of k) sX p.1
  let := stalk_field_scalar_tower (.of k) sX p.1
  let y : U := ⟨p.1, hp⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := open_stalk_scalar_tower sX U y
  let := functionField_isScalarTower X U y
  let := hU.isLocalization_stalk y
  let : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk p.1) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf y).asIdeal.primeCompl
  let bp := (topDifferential_isBaseChange k Γ(X, U) (X.presheaf.stalk p.1) n).basis bU
  have hgen : bF 0 = topDifferentialMap k (X.presheaf.stalk p.1) X.functionField n (bp 0) := by
    rw [(topDifferential_isBaseChange k Γ(X, U) (X.presheaf.stalk p.1) n).basis_apply,
      (topDifferential_isBaseChange k Γ(X, U) X.functionField n).basis_apply]
    exact (LinearMap.congr_fun (topDifferentialMap_comp k Γ(X, U)
      (X.presheaf.stalk p.1) X.functionField n) (bU 0)).symm
  obtain ⟨cp, a', ha', hc, hDa'⟩ := hD p
  rw [hDa']
  exact canonical_local_order_unique sX n p ω cp bp a' a hω ha' ha hc
    (heq.trans (congrArg (fun v => a • v) hgen))

end CanonicalCartierProof
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne

lemma canonicalModel_isCartier {n : ℕ} (X : CanonicalModel n)
    (hX : IsSmoothNfold X.toComplexProjectiveVariety n) : IsCartierDivisor X.canonical := by
  let : SmoothOfRelativeDimension n X.structureMap := hX
  exact isCartier_of_isCanonical X.structureMap n ⟨X.form, X.canonical_of_form⟩

noncomputable def smoothCanonicalClass {n : ℕ} (X : CanonicalModel n)
    (hX : IsSmoothNfold X.toComplexProjectiveVariety n) :
    cartierDivisors (X := X.scheme) := ⟨X.canonical, canonicalModel_isCartier X hX⟩

section PartialCanonicalCompatibility
variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

instance partialIsoSourceNonempty (φ : X.PartialIso Y) : Nonempty φ.source :=
  φ.dense_source.nonempty.to_subtype

instance partialIsoTargetNonempty (φ : X.PartialIso Y) : Nonempty φ.target :=
  φ.dense_target.nonempty.to_subtype

instance partialIsoSourceDominant (φ : X.PartialIso Y) : IsDominant φ.source.ι := by
  constructor
  simpa only [DenseRange, Scheme.Opens.range_ι] using φ.dense_source

instance partialIsoTargetDominant (φ : X.PartialIso Y) : IsDominant φ.target.ι := by
  constructor
  simpa only [DenseRange, Scheme.Opens.range_ι] using φ.dense_target

end PartialCanonicalCompatibility

def CompatibleCanonicalData {n : ℕ} (X Y : CanonicalModel n)
    (φ : X.scheme.PartialIso Y.scheme)
    (hφ : φ.IsOver X.structureMap Y.structureMap) : Prop :=
  rationalTopFormPullback (.of ℂ) (φ.source.ι ≫ X.structureMap) X.structureMap
      φ.source.ι rfl n X.form =
    rationalTopFormPullback (.of ℂ) (φ.source.ι ≫ X.structureMap) Y.structureMap
      (φ.iso.hom ≫ φ.target.ι) (by simpa only [Category.assoc] using hφ) n Y.form

def NoExtractionOn {X Y : Scheme} (φ : X.PartialIso Y) : Prop :=
  ∀ p : PrimeDivisor Y, p.1 ∈ φ.target

def IsKDivisorialContraction {n : ℕ} (X Y : CanonicalModel n)
    (φ : X.scheme.PartialIso Y.scheme) : Prop :=
  ∃ f : X.scheme ⟶ Y.scheme, ∃ (_ : IsDominant f),
    IsProper f ∧ φ.IsOver f (𝟙 Y.scheme) ∧
    f ≫ Y.structureMap = X.structureMap ∧
    IsElementary (X := X.toComplexProjectiveVariety) (R := Y.toComplexProjectiveVariety) f ∧
    IsRelativelyAmpleQ (X := X.toComplexProjectiveVariety) (R := Y.toComplexProjectiveVariety)
      f (-rationalWeilDivisor X.canonical) ∧
    ∃! p : PrimeDivisor X.scheme, 1 < Order.coheight (f p.1)

def IsKFlip {n : ℕ} (X Y : CanonicalModel n)
    (φ : X.scheme.PartialIso Y.scheme) : Prop :=
  ∃ R : NormalProjectiveVariety, ∃ f : X.scheme ⟶ R.scheme,
    ∃ g : Y.scheme ⟶ R.scheme, ∃ (_ : IsDominant f), ∃ (_ : IsDominant g),
      IsProper f ∧ IsProper g ∧ IsBirationalMorphism f ∧ IsBirationalMorphism g ∧
      IsSmallMorphism f ∧ IsSmallMorphism g ∧ φ.IsOver f g ∧
      f ≫ R.structureMap = X.structureMap ∧ g ≫ R.structureMap = Y.structureMap ∧
      IsElementary (X := X.toComplexProjectiveVariety) (R := R.toComplexProjectiveVariety) f ∧
      IsElementary (X := Y.toComplexProjectiveVariety) (R := R.toComplexProjectiveVariety) g ∧
      IsRelativelyAmpleQ (X := X.toComplexProjectiveVariety) (R := R.toComplexProjectiveVariety)
        f (-rationalWeilDivisor X.canonical) ∧
      IsRelativelyAmpleQ (X := Y.toComplexProjectiveVariety) (R := R.toComplexProjectiveVariety)
        g (rationalWeilDivisor Y.canonical)

def IsCanonicalMMPStep {n : ℕ} (X Y : CanonicalModel n)
    (φ : X.scheme.PartialIso Y.scheme) : Prop :=
  IsQFactorial (X := X.scheme) ∧ IsQFactorial (X := Y.scheme) ∧
  IsTerminalModel X ∧ IsTerminalModel Y ∧ NoExtractionOn φ ∧
  ∃ hφ : φ.IsOver X.structureMap Y.structureMap, CompatibleCanonicalData X Y φ hφ ∧
    (IsKDivisorialContraction X Y φ ∨ IsKFlip X Y φ)

inductive CanonicalMMPChain {n : ℕ} :
    (X Y : CanonicalModel n) → X.scheme.PartialIso Y.scheme → Prop
  | refl (X : CanonicalModel n) : CanonicalMMPChain X X (.refl X.scheme)
  | step {X Y Z : CanonicalModel n} {φ : X.scheme.PartialIso Y.scheme}
      {ψ : Y.scheme.PartialIso Z.scheme} :
      IsCanonicalMMPStep X Y φ → CanonicalMMPChain Y Z ψ →
        CanonicalMMPChain X Z (φ.trans ψ)

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne

noncomputable def canonicalModelOfSmooth (X : ComplexProjectiveVariety) (n : ℕ)
    (hX : IsSmoothNfold X n) : CanonicalModel n := by
  let : SmoothOfRelativeDimension n X.structureMap := hX
  let hK := exists_canonicalDivisor_of_smooth X.structureMap n
  let K := Classical.choose hK
  have hcanonical : IsCanonicalDivisor (.of ℂ) X.structureMap n K := Classical.choose_spec hK
  let ω := Classical.choose hcanonical
  have hω : IsCanonicalDivisorOf (.of ℂ) X.structureMap n ω K :=
    Classical.choose_spec hcanonical
  have hCartier : IsCartierDivisor K := isCartier_of_isCanonical X.structureMap n hcanonical
  exact
    { toNormalProjectiveVariety := { toComplexProjectiveVariety := X, normal := smoothNormal X hX }
      form := ω
      canonical := K
      canonical_of_form := hω
      qCartier := ⟨1, by decide, K, hCartier, by simp⟩ }

def HasEffectiveCanonicalComparison {n : ℕ} (X Y : CanonicalModel n)
    (φ : X.scheme.PartialIso Y.scheme) : Prop :=
  ∃ W : ComplexProjectiveVariety, IsSmoothNfold W n ∧
    ∃ p : W.scheme ⟶ X.scheme, ∃ q : W.scheme ⟶ Y.scheme,
      ∃ (_ : IsDominant p), ∃ (_ : IsDominant q),
        IsProper p ∧ IsProper q ∧
        p ≫ X.structureMap = W.structureMap ∧ q ≫ Y.structureMap = W.structureMap ∧
        ∃ θ : W.scheme.PartialIso X.scheme,
          θ.IsOver p (𝟙 X.scheme) ∧ (θ.trans φ).IsOver q (𝟙 Y.scheme) ∧
          ∃ P Q E : QWeilDivisor W.scheme,
            IsQCartierPullback p (rationalWeilDivisor X.canonical) P ∧
            IsQCartierPullback q (rationalWeilDivisor Y.canonical) Q ∧
            P = Q + E ∧ 0 ≤ E ∧
            (∀ F : PrimeDivisor W.scheme, E F ≠ 0 → 1 < Order.coheight (q F.1)) ∧
            (∀ F : PrimeDivisor W.scheme, Order.coheight (p F.1) = 1 →
              1 < Order.coheight (q F.1) → 0 < E F)

def HasMinimalModel {n : ℕ} (X : CanonicalModel n) : Prop :=
  ∃ Y : CanonicalModel n, IsQFactorial (X := Y.scheme) ∧ IsTerminalModel Y ∧
    IsNefQDivisor Y.toComplexProjectiveVariety (rationalWeilDivisor Y.canonical) ∧
    ∃ φ : X.scheme.PartialIso Y.scheme,
      CanonicalMMPChain X Y φ ∧ NoExtractionOn φ ∧
      (∃ hφ : φ.IsOver X.structureMap Y.structureMap, CompatibleCanonicalData X Y φ hφ) ∧
      HasEffectiveCanonicalComparison X Y φ

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne

theorem normal_birational_quasiFinite_local_bijective
    (R S K : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [IsLocalRing S]
    [Field K] [Algebra R S] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] [IsFractionRing R K] [IsFractionRing S K]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Algebra.QuasiFinite R S] : Function.Bijective (algebraMap R S) := by
  classical
  have hinj : Function.Injective (algebraMap R S) := by
    intro a b hab
    apply IsFractionRing.injective R K
    simpa only [IsScalarTower.algebraMap_apply R S K] using
      congrArg (algebraMap S K) hab
  have hlift (s : S) (hs : IsIntegral R s) : ∃ r, algebraMap R S r = s := by
    obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).mp hs.algebraMap
    exact ⟨r, IsFractionRing.injective S K (by
      simpa only [IsScalarTower.algebraMap_apply R S K] using hr)⟩
  let A := Algebra.EssFiniteType.subalgebra R S
  let p : Ideal A := (IsLocalRing.maximalIdeal S).comap (algebraMap A S)
  have : p.IsPrime := Ideal.comap_isPrime (algebraMap A S) _
  have hm : p.primeCompl = Algebra.EssFiniteType.submonoid R S := by
    ext a
    change (algebraMap A S a ∉ IsLocalRing.maximalIdeal S) ↔ IsUnit (algebraMap A S a)
    simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  let : IsLocalization.AtPrime S p := by
    change IsLocalization p.primeCompl S
    rw [hm]
    infer_instance
  let e : S ≃ₐ[R] Localization.AtPrime p :=
    (IsLocalization.algEquiv p.primeCompl S (Localization.AtPrime p)).restrictScalars R
  have : Algebra.QuasiFiniteAt R p :=
    (Algebra.QuasiFinite.iff_of_algEquiv e).mp inferInstance
  obtain ⟨r, hrp, hr, hnum⟩ :=
    (Algebra.zariskisMainProperty_iff (R := R)).mp (Algebra.ZariskisMainProperty.of_finiteType p)
  obtain ⟨rR, hrR⟩ := hlift (algebraMap A S r) hr.algebraMap
  have hru : IsUnit (algebraMap A S r) := by
    simpa [p, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hrp
  have hrRu : IsUnit rR := IsLocalHom.map_nonunit (f := algebraMap R S) rR (hrR ▸ hru)
  obtain ⟨u, hu⟩ := hrRu
  have hA (a : A) : ∃ b, algebraMap R S b = algebraMap A S a := by
    obtain ⟨m, hm⟩ := hnum a
    obtain ⟨b, hb⟩ := hlift (algebraMap A S (r ^ m * a)) hm.algebraMap
    refine ⟨(↑(u⁻¹) : R) ^ m * b, ?_⟩
    rw [map_mul, map_pow, hb, map_mul, map_pow, ← hrR, ← hu]
    rw [← mul_assoc, ← mul_pow, ← map_mul]
    simp
  refine ⟨hinj, fun s => ?_⟩
  obtain ⟨⟨a, t⟩, hst⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid R S) s
  obtain ⟨aR, haR⟩ := hA a
  obtain ⟨tR, htR⟩ := hA t.1
  have htu : IsUnit (algebraMap A S t.1) := t.2
  have htRu : IsUnit tR := IsLocalHom.map_nonunit (f := algebraMap R S) tR (htR ▸ htu)
  obtain ⟨v, hv⟩ := htRu
  refine ⟨aR * (↑(v⁻¹) : R), ?_⟩
  rw [map_mul, haR, ← hst, ← htR, ← hv, mul_assoc, ← map_mul]
  simp
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOne

noncomputable def openImmersionFunctionFieldEquiv {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsOpenImmersion f] :
    Y.functionField ≃+* X.functionField :=
  ((Y.presheaf.stalkCongr
    (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion f).symm)) ≪≫
    asIso (f.stalkMap (genericPoint X))).commRingCatIsoToRingEquiv

variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]

noncomputable def partialIsoFunctionFieldEquiv (φ : X.PartialIso Y) :
    X.functionField ≃+* Y.functionField :=
  (openImmersionFunctionFieldEquiv φ.source.ι).trans
    ((openImmersionFunctionFieldEquiv φ.iso.inv).trans
      (openImmersionFunctionFieldEquiv φ.target.ι).symm)

section
variable {X Y Z : Scheme} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
lemma dominantFunctionFieldMap_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsDominant f] [IsDominant g] (r : Z.functionField) :
    dominantFunctionFieldMap (f ≫ g) r =
      dominantFunctionFieldMap f (dominantFunctionFieldMap g r) := by
  let x : X := Classical.arbitrary X
  have hbase (a : Z.presheaf.stalk (g (f x))) :
      dominantFunctionFieldMap (f ≫ g) (algebraMap _ Z.functionField a) =
        dominantFunctionFieldMap f (dominantFunctionFieldMap g
          (algebraMap _ Z.functionField a)) := by
    calc
      _ = algebraMap (X.presheaf.stalk x) X.functionField ((f ≫ g).stalkMap x a) :=
        dominantFunctionFieldMap_algebraMap (f ≫ g) x a
      _ = algebraMap (X.presheaf.stalk x) X.functionField
          (f.stalkMap x (g.stalkMap (f x) a)) := by
        rw [Scheme.Hom.stalkMap_comp]
        rfl
      _ = _ := by
        rw [dominantFunctionFieldMap_algebraMap g (f x),
          dominantFunctionFieldMap_algebraMap f x]
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (Z.presheaf.stalk (g (f x))) r
  simp only [map_div₀, hbase]

lemma dominantFunctionFieldMap_id_apply (r : X.functionField) :
    dominantFunctionFieldMap (𝟙 X) r = r := by
  let x : X := Classical.arbitrary X
  have hbase (a : X.presheaf.stalk x) :
      dominantFunctionFieldMap (𝟙 X) (algebraMap _ X.functionField a) =
        algebraMap _ X.functionField a := by
    calc
      _ = algebraMap (X.presheaf.stalk x) X.functionField (Scheme.Hom.stalkMap (𝟙 X) x a) :=
        dominantFunctionFieldMap_algebraMap (𝟙 X) x a
      _ = _ := by rw [Scheme.Hom.stalkMap_id]; rfl
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (X.presheaf.stalk x) r
  simp only [map_div₀, hbase]

lemma partialIso_dominantFunctionFieldMap (f : X ⟶ Y) [IsDominant f]
    (φ : X.PartialIso Y) (hφ : φ.IsOver f (𝟙 Y)) (r : Y.functionField) :
    partialIsoFunctionFieldEquiv φ (dominantFunctionFieldMap f r) = r := by
  apply (openImmersionFunctionFieldEquiv φ.target.ι).injective
  simp only [partialIsoFunctionFieldEquiv, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply]
  change dominantFunctionFieldMap φ.iso.inv
      (dominantFunctionFieldMap φ.source.ι (dominantFunctionFieldMap f r)) =
    dominantFunctionFieldMap φ.target.ι r
  rw [← dominantFunctionFieldMap_comp_apply, ← dominantFunctionFieldMap_comp_apply]
  have heq : φ.iso.inv ≫ φ.source.ι ≫ f = φ.target.ι := by
    simpa [Scheme.PartialIso.IsOver, Scheme.PartialIso.symm] using hφ.symm
  simp only [Category.assoc, heq]

end

theorem birational_quasiFinite_stalk_coheight
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f]
    (hb : IsBirationalMorphism f) (x : X)
    (hq : letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
      Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :
    Order.coheight (f x) = Order.coheight x := by
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
  let : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hq
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have he := normal_birational_quasiFinite_local_bijective
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) X.functionField
  apply WithBot.coe_injective
  rw [← ringKrullDim_stalk_eq_coheight, ← ringKrullDim_stalk_eq_coheight]
  exact (RingEquiv.ofBijective (f.stalkMap x).hom he).ringKrullDim
end NumericalDimensionOne

end OAI
