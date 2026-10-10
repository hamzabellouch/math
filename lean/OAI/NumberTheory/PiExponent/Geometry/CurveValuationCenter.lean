import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole
import OAI.NumberTheory.PiExponent.LocalAlgebra.DVRValuationUnique

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveValuationCenter
open PiExponent.CurveZeroPole

theorem integral_mem_valuationSubring
    {R E Γ : Type*} [CommRing R] [Field E] [LinearOrderedCommGroupWithZero Γ]
    [Algebra R E] (v : Valuation E Γ)
    (hR : ∀ r : R, algebraMap R E r ∈ v.valuationSubring)
    {x : E} (hx : IsIntegral R x) : x ∈ v.valuationSubring := by
  let φ : R →+* v.valuationSubring :=
    { toFun := fun r => ⟨algebraMap R E r, hR r⟩
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := by intros; ext; simp
      map_mul' := by intros; ext; simp }
  let : Algebra R v.valuationSubring := φ.toAlgebra
  let : IsScalarTower R v.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (Valuation.valuationSubring.integers v).mem_of_integral hx.tower_top

theorem aeval_mem_valuationSubring
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (f : E) (hf : 0 ≤ v f) (p : F[X]) :
    Polynomial.aeval f p ∈ v.toValuation.valuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact v.toValuation.valuationSubring.toSubring.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact v.toValuation.valuationSubring.toSubring.mul_mem (hF a)
      (v.toValuation.valuationSubring.toSubring.pow_mem hf n)

theorem parameterChart_mem_valuationSubring
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    (x : E) ∈ v.toValuation.valuationSubring := by
  let := parameterPolynomialAlgebra f hf
  apply integral_mem_valuationSubring v.toValuation
    (fun p => ?_) x.property
  rw [parameterPolynomialAlgebra_map f hf p]
  exact aeval_mem_valuationSubring v hF f hvf p

def parameterChartValuationHom
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : parameterChart f hf →+* v.toValuation.valuationSubring where
  toFun x := ⟨x, parameterChart_mem_valuationSubring f hf v hF hvf x⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def parameterValuationCenter
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : Ideal (parameterChart f hf) :=
  (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
    (parameterChartValuationHom f hf v hF hvf)

instance parameterValuationCenter_isPrime
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : (parameterValuationCenter f hf v hF hvf).IsPrime :=
  inferInstanceAs (Ideal.comap _ (IsLocalRing.maximalIdeal _)).IsPrime

theorem mem_parameterValuationCenter_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    x ∈ parameterValuationCenter f hf v hF hvf ↔ 0 < v (x : E) := by
  change parameterChartValuationHom f hf v hF hvf x ∈
    IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔ _
  exact v.toValuation.mem_maximalIdeal_iff

theorem parameterValuationCenter_liesOver
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) :
    letI := parameterPolynomialAlgebra f hf
    (parameterValuationCenter f hf v hF hvf.le).LiesOver (zeroPrime F) := by
  let := parameterPolynomialAlgebra f hf
  constructor
  apply (zeroPrime_isMaximal F).eq_of_le
  · exact Ideal.IsPrime.ne_top inferInstance
  rw [zeroPrime_eq_span_X, Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
  rw [mem_parameterValuationCenter_iff]
  change 0 < v (algebraMap F[X] E Polynomial.X)
  rw [parameterPolynomialAlgebra_map f hf Polynomial.X, Polynomial.aeval_X]
  exact hvf

def parameterCenterPlace
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) : parameterZeroPlaces f hf :=
  let := parameterPolynomialAlgebra f hf
  let := parameterValuationCenter_liesOver f hf v hF hvf
  Ideal.primesOver.mk (zeroPrime F) (parameterValuationCenter f hf v hF hvf.le)

def parameterCenterLocalHom
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) :
    Localization.AtPrime (parameterValuationCenter f hf v hF hvf) →+*
      v.toValuation.valuationSubring :=
  IsLocalization.lift (M := (parameterValuationCenter f hf v hF hvf).primeCompl)
    (g := parameterChartValuationHom f hf v hF hvf) (fun y => by
      have hy : parameterChartValuationHom f hf v hF hvf y ∉
          IsLocalRing.maximalIdeal v.toValuation.valuationSubring := y.property
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hy)

@[simp] theorem parameterCenterLocalHom_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    parameterCenterLocalHom f hf v hF hvf
      (algebraMap (parameterChart f hf) _ x) = parameterChartValuationHom f hf v hF hvf x :=
  IsLocalization.lift_eq _ x

theorem parameterCenterLocalHom_comap_maximalIdeal
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) :
    (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
      (parameterCenterLocalHom f hf v hF hvf) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) := by
  apply (Localization.AtPrime.eq_maximalIdeal_iff_under_eq
    (I := parameterValuationCenter f hf v hF hvf)).mp
  ext x
  change parameterCenterLocalHom f hf v hF hvf
    (algebraMap (parameterChart f hf) _ x) ∈
      IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔ _
  rw [parameterCenterLocalHom_algebraMap]
  rfl

theorem parameterCenterLocalHom_coe
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) :
    (parameterCenterLocalHom f hf v hF hvf a : E) = algebraMap _ E a := by
  have hm : v.toValuation.valuationSubring.subtype.comp
      (parameterCenterLocalHom f hf v hF hvf) = algebraMap _ E := by
    apply IsLocalization.ringHom_ext (parameterValuationCenter f hf v hF hvf).primeCompl
    ext x
    simp only [RingHom.comp_apply]
    rw [parameterCenterLocalHom_algebraMap]
    exact (IsScalarTower.algebraMap_apply (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E x)
  exact RingHom.congr_fun hm a

theorem parameterCenterLocal_nonneg
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) :
    0 ≤ v (algebraMap _ E a) := by
  rw [← parameterCenterLocalHom_coe f hf v hF hvf a]
  exact (parameterCenterLocalHom f hf v hF hvf a).property

theorem parameterCenterLocal_positive
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf))
    (ha : a ∈ IsLocalRing.maximalIdeal _) : 0 < v (algebraMap _ E a) := by
  rw [← parameterCenterLocalHom_coe f hf v hF hvf a]
  apply v.toValuation.mem_maximalIdeal_iff.mp
  change a ∈ (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
    (parameterCenterLocalHom f hf v hF hvf)
  rw [parameterCenterLocalHom_comap_maximalIdeal]
  exact ha

theorem primeFieldValuation_algebraMap_localOrder
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    letI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot
      (Localization.AtPrime q.asIdeal)
    primeFieldValuation S E q (algebraMap S E a) =
      CurveLocalOrder.enatToIntegerOrder
        (IsDiscreteValuationRing.addVal (Localization.AtPrime q.asIdeal)
          (algebraMap S (Localization.AtPrime q.asIdeal) a)) := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  change CurveLocalOrder.fractionAddValuation A E (algebraMap S E a) = _
  rw [IsScalarTower.algebraMap_apply S A E, CurveLocalOrder.fractionAddValuation_algebraMap]
  rfl

theorem primeFieldValuation_algebraMap_nonneg
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    0 ≤ primeFieldValuation S E q (algebraMap S E a) := by
  rw [primeFieldValuation_algebraMap_localOrder]
  exact CurveLocalOrder.enatToIntegerOrder_monotone (show (0 : ℕ∞) ≤ _ from zero_le)

theorem enatToIntegerOrder_pos_iff (n : ℕ∞) :
    0 < CurveLocalOrder.enatToIntegerOrder n ↔ 0 < n := by
  rcases eq_or_ne n ⊤ with rfl | hn
  · simp
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hn
  rw [← hk]
  simp

theorem primeFieldValuation_positive_iff
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    0 < primeFieldValuation S E q (algebraMap S E a) ↔ a ∈ q.asIdeal := by
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot
    (Localization.AtPrime q.asIdeal)
  rw [primeFieldValuation_algebraMap_localOrder, enatToIntegerOrder_pos_iff,
    pos_iff_ne_zero, ne_eq, IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q.asIdeal) q.asIdeal]
  simp

structure NormalizedPlace (F E : Type*) [Field F] [Field E] [Algebra F E] where
  valuation : AddValuation E (WithTop ℤ)
  constants_nonneg : ∀ c : F, 0 ≤ valuation (algebraMap F E c)
  normalized : ∃ z : Eˣ, WeightedCurveDegree.integerOrder valuation z = 1

@[ext] theorem NormalizedPlace.ext
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p q : NormalizedPlace F E} (h : p.valuation = q.valuation) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem valuation_eq_parameterPlaceValuation
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) (hnormalized : ∃ z : Eˣ, WeightedCurveDegree.integerOrder v z = 1) :
    v = parameterPlaceValuation f hf (parameterCenterPlace f hf v hF hvf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let q := parameterValuationCenter f hf v hF hvf.le
  have hq : q ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F)
      (parameterCenterPlace f hf v hF hvf).property
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq A
  change v = CurveLocalOrder.fractionAddValuation A E
  apply PiExponent.DVRValuationUnique.eq_fractionAddValuation v
  · exact parameterCenterLocal_nonneg f hf v hF hvf.le
  · intro a ha _
    exact parameterCenterLocal_positive f hf v hF hvf.le a ha
  · exact hnormalized

theorem primeFieldValuation_normalized
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) :
    ∃ z : Eˣ, WeightedCurveDegree.integerOrder (primeFieldValuation S E q) z = 1 := by
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  exact PiExponent.DVRValuationUnique.fractionAddValuation_normalized

theorem parameterPlaceValuation_constants_nonneg
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) (c : F) :
    0 ≤ parameterPlaceValuation f hf q (algebraMap F E c) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  have hmap : algebraMap S E (algebraMap F[X] S (Polynomial.C c)) = algebraMap F E c := by
    rw [← IsScalarTower.algebraMap_apply F[X] S E,
      parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]
  change 0 ≤ primeFieldValuation S E (zeroFiberHeightOne F S q) (algebraMap F E c)
  rw [← hmap]
  exact primeFieldValuation_algebraMap_nonneg S E _ _

theorem parameterPlaceValuation_positive
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : 0 < parameterPlaceValuation f hf q f := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  have hmap : algebraMap S E (algebraMap F[X] S Polynomial.X) = f := by
    rw [← IsScalarTower.algebraMap_apply F[X] S E,
      parameterPolynomialAlgebra_map f hf, Polynomial.aeval_X]
  change 0 < primeFieldValuation S E (zeroFiberHeightOne F S q) f
  have hx : algebraMap F[X] S Polynomial.X ∈ q.1 := by
    apply (Ideal.mem_of_liesOver q.1 (zeroPrime F) Polynomial.X).mp
    change Polynomial.constantCoeff Polynomial.X = (0 : F)
    simp
  have hp := (primeFieldValuation_positive_iff S E (zeroFiberHeightOne F S q)
    (algebraMap F[X] S Polynomial.X)).mpr hx
  exact lt_of_lt_of_eq hp (congrArg (primeFieldValuation S E (zeroFiberHeightOne F S q)) hmap)

def parameterNormalizedPlace
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : NormalizedPlace F E where
  valuation := parameterPlaceValuation f hf q
  constants_nonneg := parameterPlaceValuation_constants_nonneg f hf q
  normalized := by
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    let := parameter_scalarTower f hf
    let := parameter_finite f hf
    let S := parameterChart f hf
    let : Module.IsTorsionFree F[X] S :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr
        (FunctionField.ringOfIntegers.algebraMap_injective F E)
    exact primeFieldValuation_normalized S E (zeroFiberHeightOne F S q)

theorem parameterCenterPlace_parameterNormalizedPlace
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    parameterCenterPlace f hf (parameterNormalizedPlace f hf q).valuation
      (parameterNormalizedPlace f hf q).constants_nonneg
      (parameterPlaceValuation_positive f hf q) = q := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  apply Subtype.ext
  apply Ideal.ext
  intro x
  change x ∈ parameterValuationCenter f hf (parameterNormalizedPlace f hf q).valuation
    (parameterNormalizedPlace f hf q).constants_nonneg _ ↔ x ∈ q.1
  rw [mem_parameterValuationCenter_iff]
  exact primeFieldValuation_positive_iff S E (zeroFiberHeightOne F S q) x

def positivePlaceEquivZeroPlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    {p : NormalizedPlace F E // 0 < p.valuation f} ≃ parameterZeroPlaces f hf where
  toFun p := parameterCenterPlace f hf p.1.valuation p.1.constants_nonneg p.2
  invFun q := ⟨parameterNormalizedPlace f hf q, parameterPlaceValuation_positive f hf q⟩
  left_inv p := by
    apply Subtype.ext
    apply NormalizedPlace.ext
    exact (valuation_eq_parameterPlaceValuation f hf p.1.valuation
      p.1.constants_nonneg p.2 p.1.normalized).symm
  right_inv q := parameterCenterPlace_parameterNormalizedPlace f hf q

theorem finite_positivePlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Set.Finite {p : NormalizedPlace F E | 0 < p.valuation f} := by
  let := parameterZeroPlacesFintype f hf
  have : Finite {p : NormalizedPlace F E // 0 < p.valuation f} :=
    Finite.of_equiv (parameterZeroPlaces f hf) (positivePlaceEquivZeroPlaces f hf).symm
  exact Set.finite_coe_iff.mp this

end PiExponent.CurveValuationCenter

end

end OAI
