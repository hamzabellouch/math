import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.NormalizationStalks

namespace OAI

/-! Intersection Lengths. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace FiniteColength
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma length_quotient_chain (N L : Submodule R M) (hNL : N ≤ L) :
    Module.length R (M ⧸ N) =
      Module.length R (L ⧸ N.comap L.subtype) + Module.length R (M ⧸ L) := by
  let i := (N.comap L.subtype).mapQ N L.subtype le_rfl
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, Submodule.mkQ_map_self]
  have he : Function.Exact i (Submodule.factor hNL) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk x = (0 : M ⧸ L) ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        exact ⟨Submodule.Quotient.mk (⟨x, hx⟩ : L), rfl⟩
      · rintro ⟨y, hy⟩
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          have hxy : (y : M) - x ∈ N := (Submodule.Quotient.eq N).mp hy
          exact (L.sub_mem y.property (hNL hxy)) |> (by simpa using ·)
  exact Module.length_eq_add_of_exact i (Submodule.factor hNL) hi
    (Submodule.factor_surjective hNL) he

lemma length_quotient_image (f : M →ₗ[R] M) (hf : Function.Injective f)
    (L : Submodule R M) :
    Module.length R (M ⧸ L.map f) =
      Module.length R (M ⧸ L) + Module.length R (M ⧸ LinearMap.range f) := by
  let i := L.mapQ (L.map f) f (Submodule.le_comap_map _ _)
  have hi : Function.Injective i := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ,
      Submodule.comap_map_eq_of_injective hf, Submodule.mkQ_map_self]
  have hle : L.map f ≤ LinearMap.range f := by
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have he : Function.Exact i (Submodule.factor hle) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk x = (0 : M ⧸ LinearMap.range f) ↔ _
      rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨Submodule.Quotient.mk y, rfl⟩
      · rintro ⟨y, hy⟩
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          have hxy : f y - x ∈ L.map f := (Submodule.Quotient.eq _).mp hy
          have hz : f y - x ∈ LinearMap.range f := hle hxy
          have hz' := (LinearMap.range f).sub_mem (LinearMap.mem_range_self f y) hz
          exact LinearMap.mem_range.mp (by simpa only [sub_sub_cancel] using hz')
  exact Module.length_eq_add_of_exact i (Submodule.factor hle) hi
    (Submodule.factor_surjective hle) he

theorem length_cokernel_restriction (f : M →ₗ[R] M) (hf : Function.Injective f)
    (L : Submodule R M) (hL : L.map f ≤ L) (hfin : IsFiniteLength R (M ⧸ L)) :
    Module.length R (M ⧸ LinearMap.range f) =
      Module.length R (L ⧸ (L.map f).comap L.subtype) := by
  have h₁ := length_quotient_image f hf L
  have h₂ := length_quotient_chain (L.map f) L hL
  have he : Module.length R (M ⧸ L) + Module.length R (M ⧸ LinearMap.range f) =
      Module.length R (M ⧸ L) +
        Module.length R (L ⧸ (L.map f).comap L.subtype) := by
    rw [← h₁, h₂, add_comm]
  exact ENat.add_right_injective_of_ne_top (Module.length_ne_top_iff.mpr hfin) he
end FiniteColength
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace TorsionLength
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [Module.Finite R M]

theorem finiteLength_of_torsion (hM : Module.IsTorsion R M) : IsFiniteLength R M := by
  obtain ⟨c, hc, hcnz⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hkill : Module.IsTorsionBySet R M (Ideal.span {c}) := by
    rw [Module.isTorsionBySet_span_singleton_iff]
    intro x
    exact Submodule.mem_annihilator.mp hc x (Submodule.mem_top)
  let : Module (R ⧸ Ideal.span {c}) M := hkill.module
  have : IsScalarTower R (R ⧸ Ideal.span {c}) M := hkill.isScalarTower
  have : Module.Finite (R ⧸ Ideal.span {c}) M :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hquot := isFiniteLength_quotient_span_singleton R hcnz
  have : IsArtinian R (R ⧸ Ideal.span {c}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hquot).2
  have : IsArtinianRing (R ⧸ Ideal.span {c}) := isArtinian_of_tower R inferInstance
  have : IsArtinian (R ⧸ Ideal.span {c}) M := inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, isArtinian_of_surjective_algebraMap
      (R := R ⧸ Ideal.span {c}) (M := M) (S := R) Ideal.Quotient.mk_surjective⟩

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem finiteLength_birational_quotient (B : Subalgebra R K) [Module.Finite R B] :
    IsFiniteLength R (B ⧸ (Algebra.linearMap R B).range) := by
  apply finiteLength_of_torsion
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    obtain ⟨c, r, hr⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) (x : K)
    refine ⟨c, ?_⟩
    change Submodule.Quotient.mk ((c : R) • x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hr
end TorsionLength
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace BirationalOrder
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem length_scalar_cokernel (j : R →ₗ[R] M) (hj : Function.Injective j)
    (a : R) (ha : Function.Injective (a • (LinearMap.id : M →ₗ[R] M)))
    (hfin : IsFiniteLength R (M ⧸ j.range)) :
    Module.length R (M ⧸ (a • (LinearMap.id : M →ₗ[R] M)).range) = Ring.ord R a := by
  let f : M →ₗ[R] M := a • LinearMap.id
  let L := j.range
  have hL : L.map f ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact L.smul_mem a hx
  have heq := FiniteColength.length_cokernel_restriction f ha L hL hfin
  let e : R ≃ₗ[R] L := LinearEquiv.ofBijective j.rangeRestrict
    ⟨(LinearMap.injective_rangeRestrict_iff j).mpr hj, j.surjective_rangeRestrict⟩
  have hmap : Submodule.map e.toLinearMap (Ideal.span {a}) = (L.map f).comap L.subtype := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hy
      change j (a * r) ∈ L.map f
      exact ⟨j r, LinearMap.mem_range_self _ _, by simp [f, ← map_smul, smul_eq_mul]⟩
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨r, rfl⟩ := hy
      refine ⟨a * r, Ideal.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
      apply Subtype.ext
      change j (a * r) = (x : M)
      simpa only [f, LinearMap.smul_apply, LinearMap.id_apply, ← map_smul,
        smul_eq_mul, Submodule.subtype_apply] using hxy
  exact heq.trans (Submodule.Quotient.equiv _ _ e hmap).length_eq.symm

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

theorem length_birational (B : Subalgebra R K) [Module.Finite R B] (a : R) (ha : a ≠ 0) :
    Module.length R (B ⧸ (Ideal.span {algebraMap R B a}).restrictScalars R) =
      Ring.ord R a := by
  let j := Algebra.linearMap R B
  have hj : Function.Injective j := by
    intro x y h
    apply IsFractionRing.injective R K
    exact congrArg (fun z : B => (z : K)) h
  have hmul : Function.Injective (a • (LinearMap.id : B →ₗ[R] B)) := by
    intro x y h
    apply Subtype.ext
    have hz := congrArg (fun z : B => (z : K)) h
    have hz' : algebraMap R K a * (x : K) = algebraMap R K a * (y : K) := by
      simpa [LinearMap.smul_apply, LinearMap.id_apply, Algebra.smul_def] using hz
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha) hz'
  have heq := length_scalar_cokernel j hj a hmul
    (TorsionLength.finiteLength_birational_quotient B)
  have hrange : (a • (LinearMap.id : B →ₗ[R] B)).range =
      (Ideal.span {algebraMap R B a}).restrictScalars R := by
    ext x
    change (∃ y : B, a • y = x) ↔ x ∈ Ideal.span {algebraMap R B a}
    rw [Ideal.mem_span_singleton]
    simp only [Algebra.smul_def, dvd_def, eq_comm]
  rwa [hrange] at heq
end BirationalOrder
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace LocalLengthDecomposition
open scoped BigOperators
open TensorProduct
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

noncomputable def quotientLocalization (I : Ideal B) (p : PrimeSpectrum (B ⧸ I)) :
    Localization.AtPrime p.asIdeal ≃ₐ[B ⧸ I]
      (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk I)) ⧸
        I.map (algebraMap B (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk I))))) := by
  let q := p.asIdeal.comap (Ideal.Quotient.mk I)
  have heq : Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl = p.asIdeal.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective p.asIdeal
  let S := Localization.AtPrime q
  have hloc : IsLocalization p.asIdeal.primeCompl (S ⧸ I.map (algebraMap B S)) :=
    heq ▸ inferInstance
  exact IsLocalization.algEquiv p.asIdeal.primeCompl _ _

theorem length_quotient_decomposition (I : Ideal B) [IsArtinianRing (B ⧸ I)]
    [Fintype (PrimeSpectrum (B ⧸ I))] :
    Module.length R (B ⧸ I) =
      ∑ p : PrimeSpectrum (B ⧸ I),
        Module.length R (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk I)) ⧸
          I.map (algebraMap B (Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk I))))) := by
  have heq := ((PrimeSpectrum.toPiLocalizationEquiv (B ⧸ I)).restrictScalars R).toLinearEquiv.length_eq
  change Module.length R (B ⧸ I) = Module.length R
    (∀ p : PrimeSpectrum (B ⧸ I), Localization.AtPrime p.asIdeal) at heq
  rw [Module.length_pi_of_fintype] at heq
  refine heq.trans (Finset.sum_congr rfl ?_)
  intro p _
  let S := Localization.AtPrime (p.asIdeal.comap (Ideal.Quotient.mk I))
  have : IsScalarTower R (B ⧸ I) (S ⧸ I.map (algebraMap B S)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ((quotientLocalization I p).restrictScalars R).toLinearEquiv.length_eq
end LocalLengthDecomposition
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace LocalResidueLength
open IsLocalRing
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [IsLocalRing R] [Module.Finite R B]

theorem isLocalHom_atPrime (q : Ideal B) [q.IsMaximal] :
    IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
  apply ((local_hom_TFAE _).out 1 5).mpr
  rw [IsScalarTower.algebraMap_eq R B (Localization.AtPrime q), ← Ideal.comap_comap]
  rw [show (maximalIdeal (Localization.AtPrime q)).comap (algebraMap B (Localization.AtPrime q)) = q
    from IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  exact eq_maximalIdeal (Ideal.IsMaximal.under R q)

theorem length_atPrime_restrict (q : Ideal B) [q.IsMaximal]
    [IsAlgClosed (ResidueField R)] (M : Type*) [AddCommGroup M]
    [Module R M] [Module (Localization.AtPrime q) M]
    [IsScalarTower R (Localization.AtPrime q) M] :
    Module.length R M = Module.length (Localization.AtPrime q) M := by
  have := isLocalHom_atPrime (R := R) q
  have : Module.Finite R q.ResidueField := Module.Finite.trans B q.ResidueField
  have : Module.Finite (ResidueField R) q.ResidueField :=
    Module.Finite.of_restrictScalars_finite R _ _
  have hdeg : Module.length (ResidueField R) q.ResidueField = 1 := by
    rw [Module.length_eq_finrank]
    simp only [Module.finrank_of_bijective_algebraMap
      IsAlgClosed.algebraMap_bijective_of_isIntegral, Nat.cast_one]
  rw [IsLocalRing.length_restrictScalars R (Localization.AtPrime q) M]
  rw [hdeg, mul_one]

theorem principal_length_atPrime (q : Ideal B) [q.IsMaximal]
    [IsAlgClosed (ResidueField R)] (a : B) :
    Module.length R (Localization.AtPrime q ⧸
      (Ideal.span {a}).map (algebraMap B (Localization.AtPrime q))) =
      Ring.ord (Localization.AtPrime q) (algebraMap B _ a) := by
  rw [length_atPrime_restrict (R := R) q]
  rw [Ideal.map_span, Set.image_singleton]
  rfl
end LocalResidueLength
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace NormalizedLocalIntersection
open scoped BigOperators
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  (B : Subalgebra R K) [Module.Finite R B]

theorem artinian_principal_quotient (a : R) (ha : a ≠ 0) :
    IsArtinianRing (B ⧸ Ideal.span {algebraMap R B a}) := by
  have heq : Module.length R (B ⧸ Ideal.span {algebraMap R B a}) = Ring.ord R a :=
    BirationalOrder.length_birational B a ha
  have hfin := Module.length_ne_top_iff.mp (heq ▸ Ring.ord_ne_top
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha))
  have : IsArtinian R (B ⧸ Ideal.span {algebraMap R B a}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  exact isArtinian_of_tower R inferInstance

theorem ord_eq_sum [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (a : R) (ha : a ≠ 0)
    [Fintype (PrimeSpectrum (B ⧸ Ideal.span {algebraMap R B a}))] :
    Ring.ord R a = ∑ p : PrimeSpectrum (B ⧸ Ideal.span {algebraMap R B a}),
      Ring.ord (Localization.AtPrime
        (p.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {algebraMap R B a}))))
        (algebraMap R _ a) := by
  let I : Ideal B := Ideal.span {algebraMap R B a}
  have : IsArtinianRing (B ⧸ I) := artinian_principal_quotient B a ha
  have hbir : Module.length R (B ⧸ I) = Ring.ord R a :=
    BirationalOrder.length_birational B a ha
  apply hbir.symm.trans
  apply (LocalLengthDecomposition.length_quotient_decomposition (R := R) I).trans
  apply Finset.sum_congr rfl
  intro p _
  let q := p.asIdeal.comap (Ideal.Quotient.mk I)
  have : p.asIdeal.IsMaximal := inferInstance
  have : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have heq := LocalResidueLength.principal_length_atPrime (R := R) q (algebraMap R B a)
  exact heq.trans (congrArg (Ring.ord (Localization.AtPrime q))
    (IsScalarTower.algebraMap_apply R B (Localization.AtPrime q) a).symm)
end NormalizedLocalIntersection
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

abbrev NormalizedStalkBranches (x : X) (a : X.presheaf.stalk x) :=
  PrimeSpectrum (integralClosure (X.presheaf.stalk x) X.functionField ⧸
    Ideal.span {algebraMap (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField) a})

theorem finite_normalizedStalkBranches (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (x : X) (hdim : Order.coheight x ≤ 1)
    (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    Finite (NormalizedStalkBranches x a) := by
  let R := X.presheaf.stalk x
  let B := integralClosure R X.functionField
  have : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hdim
  have : Module.Finite R B := finite_integralClosure_stalk sX x
  have : IsArtinianRing (B ⧸ Ideal.span {algebraMap R B a}) :=
    NormalizedLocalIntersection.artinian_principal_quotient B a ha
  infer_instance

theorem localOrder_eq_normalizedBranches (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (x : X) (hx : IsClosed ({x} : Set X))
    (hdim : Order.coheight x ≤ 1) (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    Ring.ord (X.presheaf.stalk x) a =
      ∑ᶠ q : NormalizedStalkBranches x a,
        Ring.ord (Localization.AtPrime (q.asIdeal.comap (Ideal.Quotient.mk
          (Ideal.span {algebraMap (X.presheaf.stalk x)
            (integralClosure (X.presheaf.stalk x) X.functionField) a}))))
          (algebraMap (X.presheaf.stalk x) _ a) := by
  classical
  let R := X.presheaf.stalk x
  let B := integralClosure R X.functionField
  have : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hdim
  have : Module.Finite R B := finite_integralClosure_stalk sX x
  have : IsAlgClosed (IsLocalRing.ResidueField R) :=
    IsAlgClosed.of_ringEquiv ℂ _
      (Iso.commRingCatIsoToRingEquiv (residueFieldIsoBase sX x hx)).symm
  have : Finite (NormalizedStalkBranches x a) :=
    finite_normalizedStalkBranches sX x hdim a ha
  let : Fintype (NormalizedStalkBranches x a) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  exact NormalizedLocalIntersection.ord_eq_sum B a ha
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open IsLocalRing
variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
  [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
  (a : R) (ha : a ≠ 0) (hau : ¬ IsUnit a)

noncomputable def principalFiberPrimeEquiv :
    PrimeSpectrum (B ⧸ Ideal.span {algebraMap R B a}) ≃ (maximalIdeal R).primesOver B := by
  let I : Ideal B := Ideal.span {algebraMap R B a}
  let e := I.primeSpectrumQuotientOrderIsoZeroLocus
  let e' : PrimeSpectrum.zeroLocus (I : Set B) ≃ (maximalIdeal R).primesOver B :=
    { toFun := fun q => ⟨q.1.asIdeal, q.1.isPrime, ⟨by
        have ha' : a ∈ q.1.asIdeal.under R := q.2 (Ideal.subset_span rfl)
        have hn : q.1.asIdeal.under R ≠ ⊥ := by
          intro he
          exact ha ((he ▸ ha' : a ∈ (⊥ : Ideal R)))
        exact (eq_maximalIdeal (Ideal.isMaximal_of_isPrime_of_ne_bot _ hn)).symm⟩⟩
      invFun := fun q => ⟨⟨q.1,q.2.1⟩, by
        apply (Ideal.span_singleton_le_iff_mem _).mpr
        exact (q.1.mem_of_liesOver (maximalIdeal R) a).mp
          (mem_nonunits_iff.mpr hau)⟩
      left_inv := fun q => by
        apply Subtype.ext
        rfl
      right_inv := fun q => by
        apply Subtype.ext
        rfl }
  exact e.toEquiv.trans e' 

lemma principalFiberPrimeEquiv_asIdeal
    (q : PrimeSpectrum (B ⧸ Ideal.span {algebraMap R B a})) :
    (principalFiberPrimeEquiv R B a ha hau q).1 =
      q.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {algebraMap R B a})) := by
  rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace NormalizedLocalIntersection
open scoped BigOperators
variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  (B : Subalgebra R K) [Module.Finite R B]

theorem ord_eq_finsum_branches (a : R) (ha : a ≠ 0) :
    Ring.ord R a = ∑ᶠ q : (IsLocalRing.maximalIdeal R).primesOver B,
      Ring.ord (Localization.AtPrime q.1) (algebraMap R _ a) := by
  classical
  by_cases hu : IsUnit a
  · rw [Ring.ord_of_isUnit hu]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro q
    exact Ring.ord_of_isUnit (hu.map (algebraMap R _))
  · have : IsArtinianRing (B ⧸ Ideal.span {algebraMap R B a}) :=
      artinian_principal_quotient B a ha
    let : Fintype (PrimeSpectrum (B ⧸ Ideal.span {algebraMap R B a})) := Fintype.ofFinite _
    rw [← finsum_comp_equiv (principalFiberPrimeEquiv R B a ha hu),
      finsum_eq_sum_of_fintype]
    exact ord_eq_sum B a ha
end NormalizedLocalIntersection
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem ringOrder_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : Ring.ord S (e a) = Ring.ord R a := by
  rw [Ring.ord, Ring.ord, Module.length_quotient, Module.length_quotient]
  simpa only [Ideal.comap_symm, Ideal.map_span, Set.image_singleton] using
    Ideal.coheight_comap_of_surjective e.symm e.symm.surjective (Ideal.span {a})

theorem scheme_order_of_stalk_element {C : Scheme} [IsIntegral C]
    [IsLocallyNoetherian C] (x : C) (hx : Order.coheight x = 1)
    (a : C.presheaf.stalk x) (ha : a ≠ 0) :
    C.ord (algebraMap (C.presheaf.stalk x) C.functionField a) x =
      ((Ring.ord (C.presheaf.stalk x) a).toNat : ℤ) := by
  let : Ring.KrullDimLE 1 (C.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have ha' : algebraMap (C.presheaf.stalk x) C.functionField a ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (C.presheaf.stalk x) C.functionField).ne ha
  apply (C.ord_eq_iff hx ha').mpr
  change Ring.ordFrac (C.presheaf.stalk x) _ = _
  rw [Ring.ordFrac_eq_ord _ ha]
  exact Ring.ordMonoidWithZeroHom_eq_coe (C.presheaf.stalk x) (mem_nonZeroDivisors_of_ne_zero ha)
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))).symm

theorem scheme_order_on_affine_chart {C : Scheme} [IsIntegral C]
    [IsLocallyNoetherian C] {U : C.Opens} [Nonempty U] (hU : IsAffineOpen U)
    (x : U) (hx : Order.coheight (x : C) = 1) (t : Γ(C, U)) (ht : t ≠ 0) :
    C.ord (C.germToFunctionField U t) x =
      ((Ring.ord (Localization.AtPrime (hU.primeIdealOf x).asIdeal)
        (algebraMap Γ(C, U) (Localization.AtPrime (hU.primeIdealOf x).asIdeal) t)).toNat : ℤ) := by
  let := C.presheaf.algebra_section_stalk x
  let := hU.isLocalization_stalk x
  let e := IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf x).asIdeal) (C.presheaf.stalk x)
  have ht' : (C.presheaf.germ U (x : C) x.2).hom t ≠ 0 := by
    simpa only [map_zero] using (germ_injective_of_isIntegral C x x.2).ne ht
  have ho := scheme_order_of_stalk_element (C := C) (x : C) hx ((C.presheaf.germ U (x : C) x.2).hom t) ht'
  rw [C.algebraMap_germ_eq_germToFunctionField x.2 t] at ho
  apply ho.trans
  have he := ringOrder_equiv e.toRingEquiv
    (algebraMap Γ(C, U) (Localization.AtPrime (hU.primeIdealOf x).asIdeal) t)
  have hc : e.toRingEquiv
      (algebraMap Γ(C, U) (Localization.AtPrime (hU.primeIdealOf x).asIdeal) t) =
      (C.presheaf.germ U (x : C) x.2).hom t := e.commutes t
  rw [hc] at he
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) he

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem localOrder_eq_normalizationFiber (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (x : X) (hx : IsClosed ({x} : Set X))
    (hdim : Order.coheight x ≤ 1) (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
    Ring.ord (X.presheaf.stalk x) a =
      ∑ᶠ y : {y : N // f y = x},
        Ring.ord (N.presheaf.stalk y.1) (fiberStalkMap f x y a) := by
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let R := X.presheaf.stalk x
  let K := X.functionField
  let B := integralClosure R K
  have : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hdim
  have : Module.Finite R B := finite_integralClosure_stalk sX x
  have : IsAlgClosed (IsLocalRing.ResidueField R) :=
    IsAlgClosed.of_ringEquiv ℂ _
      (Iso.commRingCatIsoToRingEquiv (residueFieldIsoBase sX x hx)).symm
  obtain ⟨U,hU,hxU,_⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let E := genericNormalizationFiberEquiv U hU ⟨x,hxU⟩
  have hsum := NormalizedLocalIntersection.ord_eq_finsum_branches B a ha
  rw [← finsum_comp_equiv E.symm] at hsum
  apply hsum.trans
  apply finsum_congr
  intro y
  let S := N.presheaf.stalk y.1
  let hf := genericNormalization_bijective_functionField (X := X)
  let : Algebra R S := (fiberStalkMap f x y).toAlgebra
  let : Algebra S K := (birationalStalkToField f hf y.1).toAlgebra
  have : IsFractionRing S K := birationalStalk_isFractionRing f hf y.1
  have : IsScalarTower R S K := birationalFiberStalk_tower f hf x y
  have : IsIntegrallyClosed S := (genericNormalization_stalk y.1).2
  let : Algebra B S := (integralClosureToNormal R S K).toRingHom.toAlgebra
  have : IsLocalization.AtPrime S (E.symm y).1 :=
    genericNormalization_stalk_atPrime sX U hU ⟨x,hxU⟩ y
  let e := IsLocalization.algEquiv (E.symm y).1.primeCompl
    (Localization.AtPrime (E.symm y).1) S
  have he : e.toRingEquiv (algebraMap R (Localization.AtPrime (E.symm y).1) a) =
      fiberStalkMap f x y a := by
    change e (algebraMap R (Localization.AtPrime (E.symm y).1) a) = _
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime (E.symm y).1),
      e.commutes]
    exact (integralClosureToNormal R S K).commutes a
  have ho := ringOrder_equiv e.toRingEquiv
    (algebraMap R (Localization.AtPrime (E.symm y).1) a)
  rw [he] at ho
  exact ho.symm

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem localOrder_int_eq_normalizationFiber (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (x : X) (hx : IsClosed ({x} : Set X))
    (hdim : Order.coheight x ≤ 1) (a : X.presheaf.stalk x) (ha : a ≠ 0) :
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ((Ring.ord (X.presheaf.stalk x) a).toNat : ℤ) =
      ∑ᶠ y : {y : N // f y = x},
        ((Ring.ord (N.presheaf.stalk y.1) (fiberStalkMap f x y a)).toNat : ℤ) := by
  classical
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let f := (X.fromSpecStalk (genericPoint X)).fromNormalization
  have : AlgebraicGeometry.IsFinite f := finite_genericNormalization sX
  have hfin : ({y : N | f y = x}).Finite := f.finite_preimage_singleton x
  have : Finite {y : N // f y = x} := hfin.to_subtype
  let : Fintype {y : N // f y = x} := Fintype.ofFinite _
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hdim
  have heq := localOrder_eq_normalizationFiber sX x hx hdim a ha
  dsimp only at heq ⊢
  rw [finsum_eq_sum_of_fintype] at heq ⊢
  have htop : (∑ y : {y : N // f y = x},
      Ring.ord (N.presheaf.stalk y.1) (fiberStalkMap f x y a)) ≠ ⊤ := by
    rw [← heq]
    exact Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr ha)
  have hn := congrArg ENat.toNat heq
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp htop)] at hn
  exact_mod_cast hn
end NumericalDimensionOne

end OAI
