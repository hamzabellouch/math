import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.WeightedCurveDegree
import OAI.NumberTheory.PiExponent.Jets.IntrinsicLength

namespace OAI

open scoped BigOperators nonZeroDivisors
open IsLocalRing IsDiscreteValuationRing

namespace PiExponent.CurveLocalOrder

theorem length_quotient_span_eq_addVal
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal A a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ]
  rw [Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal A n

def enatToIntegerOrder : ℕ∞ →+ WithTop ℤ where
  toFun := ENat.map (fun n : ℕ => (n : ℤ))
  map_zero' := by simp
  map_add' a b := ENat.map_add (Nat.castAddMonoidHom ℤ) a b

@[simp] theorem enatToIntegerOrder_top : enatToIntegerOrder ⊤ = ⊤ := rfl

@[simp] theorem enatToIntegerOrder_natCast (n : ℕ) :
    enatToIntegerOrder n = (n : WithTop ℤ) := rfl

@[simp] theorem enatToIntegerOrder_eq_top_iff (n : ℕ∞) :
    enatToIntegerOrder n = ⊤ ↔ n = ⊤ := ENat.map_eq_top_iff

theorem enatToIntegerOrder_monotone : Monotone enatToIntegerOrder := by
  apply ENat.monotone_map_iff.mpr
  intro m n h
  change (m : ℤ) ≤ (n : ℤ)
  exact_mod_cast h

noncomputable def localAddValuation
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    AddValuation A (WithTop ℤ) :=
  (IsDiscreteValuationRing.addVal A).map enatToIntegerOrder
    enatToIntegerOrder_top enatToIntegerOrder_monotone

@[simp] theorem localAddValuation_apply
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (a : A) :
    localAddValuation A a = enatToIntegerOrder (IsDiscreteValuationRing.addVal A a) := rfl

@[simp] theorem localAddValuation_eq_top_iff
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (a : A) :
    localAddValuation A a = ⊤ ↔ a = 0 := by
  rw [localAddValuation_apply, enatToIntegerOrder_eq_top_iff,
    IsDiscreteValuationRing.addVal_eq_top_iff]

theorem nonZeroDivisors_le_primeCompl
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    nonZeroDivisors A ≤ (localAddValuation A).toValuation.supp.primeCompl := by
  intro a ha
  change localAddValuation A a ≠ ⊤
  rw [ne_eq, localAddValuation_eq_top_iff]
  exact mem_nonZeroDivisors_iff_ne_zero.mp ha

noncomputable def fractionAddValuation
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] : AddValuation K (WithTop ℤ) :=
  AddValuation.ofValuation
    ((localAddValuation A).toValuation.extendToLocalization
      (nonZeroDivisors_le_primeCompl A) K)

@[simp] theorem fractionAddValuation_algebraMap
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (a : A) :
    fractionAddValuation A K (algebraMap A K a) = localAddValuation A a := by
  exact Valuation.extendToLocalization_apply_map_apply
    (localAddValuation A).toValuation (nonZeroDivisors_le_primeCompl A) K a

theorem fraction_order_eq_principal_colength
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {a : A} (ha : a ≠ 0) :
    fractionAddValuation A K (algebraMap A K a) =
      enatToIntegerOrder (Module.length A (A ⧸ Ideal.span {a})) := by
  rw [fractionAddValuation_algebraMap, localAddValuation_apply,
    length_quotient_span_eq_addVal ha]

theorem principal_colength_ne_top
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha : a ≠ 0) : Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤ := by
  rw [length_quotient_span_eq_addVal ha]
  exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr ha

theorem integerOrder_field_image_eq_length
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {a : A} (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (fractionAddValuation A K)
      (Units.mk0 (algebraMap A K a) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha)) =
        ((Module.length A (A ⧸ Ideal.span {a})).toNat : ℤ) := by
  apply WithTop.coe_injective
  rw [WeightedCurveDegree.coe_integerOrder]
  change fractionAddValuation A K (algebraMap A K a) = _
  rw [fraction_order_eq_principal_colength ha]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (principal_colength_ne_top ha)
  rw [← hn]
  simp

theorem atPrime_principal_colength
    {S : Type*} [CommRing S] [IsDedekindDomain S]
    (q : IsDedekindDomain.HeightOneSpectrum S) {a : S} (ha : a ≠ 0) :
    let A := Localization.AtPrime q.asIdeal
    letI : IsDiscreteValuationRing A :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
    Module.length A (A ⧸ Ideal.span {algebraMap S A a}) =
      IsDiscreteValuationRing.addVal A (algebraMap S A a) := by
  dsimp only
  let : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot _
  apply length_quotient_span_eq_addVal
  exact (map_ne_zero_iff _ (IsLocalization.injective
    (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha

theorem ramificationIdx_eq_local_order
    {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] (t : R) (q : Ideal S) [q.IsPrime]
    [q.LiesOver (Ideal.span {t})] (hq : q ≠ ⊥)
    (ht : algebraMap R (Localization.AtPrime q) t ≠ 0) :
    letI : IsDiscreteValuationRing (Localization.AtPrime q) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq _
    q.ramificationIdx R =
      (IsDiscreteValuationRing.addVal (Localization.AtPrime q)
        (algebraMap R (Localization.AtPrime q) t)).toNat := by
  let : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq _
  rw [Ideal.ramificationIdx_eq (Ideal.span {t}) q,
    Ideal.map_span, Set.image_singleton, length_quotient_span_eq_addVal ht]

theorem finite_over_coefficient_field_of_finite_length
    {F A M : Type*} [Field F] [CommRing A] [Algebra F A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
    (ε : A →+* F) (hε : ∀ c : F, ε (algebraMap F A c) = c)
    (hM : IsFiniteLength A M) : Module.Finite F M := by
  have hlength := PiExponentJets.W24.length_eq_coefficient_length ε hε hM
  have hF : IsFiniteLength F M := Module.length_ne_top_iff.mp (by
    rw [← hlength]
    exact Module.length_ne_top_iff.mpr hM)
  let : IsNoetherian F M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hF).1
  infer_instance

theorem principal_quotient_finite_over_coefficient_field
    {F A : Type*} [Field F] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra F A] (ε : A →+* F) (hε : ∀ c : F, ε (algebraMap F A c) = c)
    {a : A} (ha : a ≠ 0) : Module.Finite F (A ⧸ Ideal.span {a}) := by
  exact finite_over_coefficient_field_of_finite_length ε hε
    (Module.length_ne_top_iff.mp (principal_colength_ne_top ha))

theorem principal_quotient_finrank_eq_order
    {F A : Type*} [Field F] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra F A] (ε : A →+* F) (hε : ∀ c : F, ε (algebraMap F A c) = c)
    {a : A} (ha : a ≠ 0) :
    (Module.finrank F (A ⧸ Ideal.span {a}) : ℕ∞) = IsDiscreteValuationRing.addVal A a := by
  let := principal_quotient_finite_over_coefficient_field ε hε ha
  rw [← PiExponentJets.W24.module_length_eq_finrank_of_augmentation ε hε]
  exact length_quotient_span_eq_addVal ha

noncomputable def residueCoefficientEquiv
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] :
    F ≃ₐ[F] IsLocalRing.ResidueField A :=
  AlgEquiv.ofBijective (Algebra.ofId F (IsLocalRing.ResidueField A))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

noncomputable def residueAugmentation
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] : A →+* F :=
  (residueCoefficientEquiv F A).symm.toRingHom.comp (IsLocalRing.residue A)

@[simp] theorem residueAugmentation_algebraMap
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] (c : F) :
    residueAugmentation F A (algebraMap F A c) = c := by
  change (residueCoefficientEquiv F A).symm
    (algebraMap A (IsLocalRing.ResidueField A) (algebraMap F A c)) = c
  rw [← IsScalarTower.algebraMap_apply F A (IsLocalRing.ResidueField A)]
  exact (residueCoefficientEquiv F A).symm.commutes c

theorem principal_quotient_finrank_eq_order_of_algClosed
    {F A : Type*} [Field F] [IsAlgClosed F] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra F A]
    [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] {a : A} (ha : a ≠ 0) :
    (Module.finrank F (A ⧸ Ideal.span {a}) : ℕ∞) = IsDiscreteValuationRing.addVal A a :=
  principal_quotient_finrank_eq_order (residueAugmentation F A)
    (residueAugmentation_algebraMap F A) ha

end PiExponent.CurveLocalOrder

end OAI
