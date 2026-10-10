import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap
import OAI.NumberTheory.PiExponent.Geometry.PlaceParameterModel

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveModelPlaces
universe u
open CurveZeroPole CurveValuationCenter WeightedCurveDegree
open CurveNormalizationModel PlaceParameterModel
open AlgebraicGeometry CategoryTheory

theorem parameterValuationCenter_ne_bot
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    parameterValuationCenter f hf p.valuation p.constants_nonneg hp ≠ ⊥ := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective S (parameter p)
  have hbE : algebraMap S E b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  have haE : algebraMap S E a ≠ 0 := by
    intro ha
    rw [ha, zero_div] at hab
    exact parameter_nonzero p hab.symm
  have hbval : 0 ≤ p.valuation (algebraMap S E b) :=
    parameterChart_mem_valuationSubring f hf p.valuation p.constants_nonneg hp b
  have hmul : parameter p * algebraMap S E b = algebraMap S E a :=
    (eq_div_iff hbE).mp hab.symm
  have hapos : 0 < p.valuation (algebraMap S E a) := by
    rw [← hmul, p.valuation.map_mul, parameter_value]
    exact lt_of_lt_of_le (by norm_num : (0 : WithTop ℤ) < 1)
      (le_add_of_nonneg_right hbval)
  have hamem : a ∈ parameterValuationCenter f hf p.valuation p.constants_nonneg hp :=
    (mem_parameterValuationCenter_iff f hf p.valuation p.constants_nonneg hp a).mpr hapos
  intro hzero
  rw [hzero, Ideal.mem_bot] at hamem
  exact haE (by rw [hamem, map_zero])

def chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    IsDedekindDomain.HeightOneSpectrum (parameterChart f hf) where
  asIdeal := parameterValuationCenter f hf p.valuation p.constants_nonneg hp
  isPrime := inferInstance
  ne_bot := parameterValuationCenter_ne_bot f hf p hp

def chartValuation
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    AddValuation E (WithTop ℤ) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  primeFieldValuation (parameterChart f hf) E q

theorem valuation_eq_chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    p.valuation = chartValuation f hf (chartCenter f hf p hp) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let q := parameterValuationCenter f hf p.valuation p.constants_nonneg hp
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (parameterValuationCenter_ne_bot f hf p hp) A
  change p.valuation = CurveLocalOrder.fractionAddValuation A E
  apply DVRValuationUnique.eq_fractionAddValuation p.valuation
  · exact parameterCenterLocal_nonneg f hf p.valuation p.constants_nonneg hp
  · intro a ha _
    exact parameterCenterLocal_positive f hf p.valuation p.constants_nonneg hp a ha
  · exact p.normalized

theorem chartValuation_nonneg
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf))
    (a : parameterChart f hf) : 0 ≤ chartValuation f hf q (a : E) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact primeFieldValuation_algebraMap_nonneg (parameterChart f hf) E q a

theorem chartValuation_positive_iff
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf))
    (a : parameterChart f hf) : 0 < chartValuation f hf q (a : E) ↔ a ∈ q.asIdeal := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact primeFieldValuation_positive_iff (parameterChart f hf) E q a

def chartPlace
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    NormalizedPlace F E where
  valuation := chartValuation f hf q
  constants_nonneg c := by
    let := parameterPolynomialAlgebra f hf
    have hmap : ((algebraMap F[X] (parameterChart f hf) (Polynomial.C c)) : E) =
        algebraMap F E c := by
      change algebraMap F[X] E (Polynomial.C c) = _
      rw [parameterPolynomialAlgebra_map, Polynomial.aeval_C]
    rw [← hmap]
    exact chartValuation_nonneg f hf q _
  normalized := by
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    let := parameter_scalarTower f hf
    let := parameter_finite f hf
    exact primeFieldValuation_normalized (parameterChart f hf) E q

theorem chartPlace_parameter_nonneg
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    0 ≤ (chartPlace f hf q).valuation f := by
  let := parameterPolynomialAlgebra f hf
  have hmap : ((algebraMap F[X] (parameterChart f hf) Polynomial.X) : E) = f := by
    change algebraMap F[X] E Polynomial.X = f
    rw [parameterPolynomialAlgebra_map, Polynomial.aeval_X]
  have hn := chartValuation_nonneg f hf q
    (algebraMap F[X] (parameterChart f hf) Polynomial.X)
  exact (congrArg (fun x : E => 0 ≤ chartValuation f hf q x) hmap).mp hn

@[simp] theorem chartPlace_chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    chartPlace f hf (chartCenter f hf p hp) = p :=
  NormalizedPlace.ext (valuation_eq_chartCenter f hf p hp).symm

@[simp] theorem chartCenter_chartPlace
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    chartCenter f hf (chartPlace f hf q) (chartPlace_parameter_nonneg f hf q) = q := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext a
  exact (mem_parameterValuationCenter_iff f hf (chartPlace f hf q).valuation
    (chartPlace f hf q).constants_nonneg (chartPlace_parameter_nonneg f hf q) a).trans
      (chartValuation_positive_iff f hf q a)

def regularPlacesEquivChartPrimes
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    {p : NormalizedPlace F E // 0 ≤ p.valuation f} ≃
      IsDedekindDomain.HeightOneSpectrum (parameterChart f hf) where
  toFun p := chartCenter f hf p.1 p.2
  invFun q := ⟨chartPlace f hf q, chartPlace_parameter_nonneg f hf q⟩
  left_inv p := Subtype.ext (chartPlace_chartCenter f hf p.1 p.2)
  right_inv q := chartCenter_chartPlace f hf q

theorem parameterLaurentMap_mem
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹)
    (a : LaurentPolynomial F) :
    parameterLaurentMap f hf a ∈ p.valuation.toValuation.valuationSubring := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add]
    exact p.valuation.toValuation.valuationSubring.toSubring.add_mem ha hb
  | C_mul_T n c =>
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      rw [parameterLaurentMap, LaurentPolynomial.eval₂_C_mul_T_n]
      exact p.valuation.toValuation.valuationSubring.toSubring.mul_mem
        (p.constants_nonneg c)
        (p.valuation.toValuation.valuationSubring.toSubring.pow_mem hp n)
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_not_ge hn)
      rw [parameterLaurentMap, LaurentPolynomial.eval₂_C_mul_T_neg_n]
      exact p.valuation.toValuation.valuationSubring.toSubring.mul_mem
        (p.constants_nonneg c)
        (p.valuation.toValuation.valuationSubring.toSubring.pow_mem hpinv k)

theorem parameterLaurentChart_mem
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹)
    (a : parameterLaurentChart f hf) :
    (a : E) ∈ p.valuation.toValuation.valuationSubring := by
  let := parameterLaurentAlgebra f hf
  exact integral_mem_valuationSubring p.valuation.toValuation
    (parameterLaurentMap_mem f hf p hp hpinv) a.property

def laurentValuationHom
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    parameterLaurentChart f hf →+* p.valuation.toValuation.valuationSubring where
  toFun a := ⟨a, parameterLaurentChart_mem f hf p hp hpinv a⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def laurentCenter
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    PrimeSpectrum (parameterLaurentChart f hf) :=
  ⟨(IsLocalRing.maximalIdeal p.valuation.toValuation.valuationSubring).comap
    (laurentValuationHom f hf p hp hpinv), inferInstance⟩

theorem laurentCenter_zero
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    zeroOverlap f hf (laurentCenter f hf p hp hpinv) =
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  ext a
  rfl

theorem laurentCenter_infinity
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    infinityOverlap f hf (laurentCenter f hf p hp hpinv) =
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hpinv, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  ext a
  rfl

theorem center_images_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ =
    infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hpinv, inferInstance⟩ := by
  rw [← laurentCenter_zero f hf p hp hpinv, ← laurentCenter_infinity f hf p hp hpinv]
  exact congrArg (fun g => g (laurentCenter f hf p hp hpinv))
    (parameterCurve_overlap_compatibility f hf)

theorem regular_iff_inverse_not_positive
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (f : E) (hf : f ≠ 0) :
    0 ≤ p.valuation f ↔ ¬ 0 < p.valuation f⁻¹ := by
  let z := Units.mk0 f hf
  change 0 ≤ p.valuation (z : E) ↔ ¬ 0 < p.valuation ((z : E)⁻¹)
  rw [← Units.val_inv_eq_inv_val, ← coe_integerOrder, ← coe_integerOrder, integerOrder_inv]
  change ((0 : ℤ) : WithTop ℤ) ≤ (integerOrder p.valuation z : WithTop ℤ) ↔
    ¬ ((0 : ℤ) : WithTop ℤ) < (-integerOrder p.valuation z : ℤ)
  rw [WithTop.coe_le_coe, WithTop.coe_lt_coe]
  omega

theorem inverse_positive_of_not_regular
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (f : E) (hf : f ≠ 0)
    (hp : ¬ 0 ≤ p.valuation f) : 0 < p.valuation f⁻¹ := by
  exact Classical.not_not.mp ((not_congr (regular_iff_inverse_not_positive p f hf)).mp hp)

def placePoint
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) : parameterCurve f hf :=
  if hp : 0 ≤ p.valuation f then
    zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩
  else
    infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg (inverse_positive_of_not_regular p f hf.ne_zero hp).le,
        inferInstance⟩

theorem placePoint_eq_zero
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) :
    placePoint f hf p = zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  simp only [placePoint, dite_eq_left hp]

theorem placePoint_eq_infinity
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f⁻¹) :
    placePoint f hf p = infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  by_cases h : 0 ≤ p.valuation f
  · rw [placePoint_eq_zero f hf p h]
    exact center_images_eq f hf p h hp
  · simp only [placePoint, dite_eq_right h]

theorem placePoint_ne_genericPoint
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) : placePoint f hf p ≠ genericPoint (parameterCurve f hf) := by
  by_cases hp : 0 ≤ p.valuation f
  · rw [placePoint_eq_zero f hf p hp]
    intro h
    have hq := (zeroChartInclusion f hf).injective
      (h.trans (genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)).symm)
    rw [genericPoint_eq_bot_of_affine] at hq
    exact parameterValuationCenter_ne_bot f hf p hp (congrArg PrimeSpectrum.asIdeal hq)
  · let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    have hi := (inverse_positive_of_not_regular p f hf.ne_zero hp).le
    rw [placePoint_eq_infinity f hf p hi]
    intro h
    have hq := (infinityChartInclusion f hf).injective
      (h.trans (genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)).symm)
    rw [genericPoint_eq_bot_of_affine] at hq
    exact parameterValuationCenter_ne_bot f⁻¹ (transcendental_inverse f hf) p hi
      (congrArg PrimeSpectrum.asIdeal hq)

theorem regular_center_injective
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p q : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) (hq : 0 ≤ q.valuation f)
    (h : parameterValuationCenter f hf p.valuation p.constants_nonneg hp =
      parameterValuationCenter f hf q.valuation q.constants_nonneg hq) : p = q := by
  have hc : chartCenter f hf p hp = chartCenter f hf q hq :=
    IsDedekindDomain.HeightOneSpectrum.ext h
  calc
    p = chartPlace f hf (chartCenter f hf p hp) := (chartPlace_chartCenter f hf p hp).symm
    _ = chartPlace f hf (chartCenter f hf q hq) := congrArg (chartPlace f hf) hc
    _ = q := chartPlace_chartCenter f hf q hq

theorem placePoint_mem_zero_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    placePoint f hf p ∈ Set.range (zeroChartInclusion f hf) ↔ 0 ≤ p.valuation f := by
  constructor
  · intro h
    by_contra hp
    have hi := inverse_positive_of_not_regular p f hf.ne_zero hp
    let q : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)) :=
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hi.le, inferInstance⟩
    have he : placePoint f hf p = infinityChartInclusion f hf q :=
      placePoint_eq_infinity f hf p hi.le
    have hm : infinityChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf) := he ▸ h
    have ho := (infinityChart_mem_zero_iff f hf q).mp hm
    let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    have h := (congrArg (fun s => q ∈ s) (infinityOverlap_range f hf)).mp ho
    change algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X ∉
      parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hi.le at h
    apply h
    rw [mem_parameterValuationCenter_iff]
    have hmap : ((algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf))
        Polynomial.X) : E) = f⁻¹ := by
      change algebraMap F[X] E Polynomial.X = f⁻¹
      rw [parameterPolynomialAlgebra_map, Polynomial.aeval_X]
    exact (congrArg (fun a : E => 0 < p.valuation a) hmap).mpr hi
  · intro hp
    rw [placePoint_eq_zero f hf p hp]
    exact ⟨_, rfl⟩

theorem placePoint_injective
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Function.Injective (placePoint f hf) := by
  intro p q h
  have hreg : (0 ≤ p.valuation f) ↔ (0 ≤ q.valuation f) := by
    rw [← placePoint_mem_zero_iff f hf p, ← placePoint_mem_zero_iff f hf q, h]
  by_cases hp : 0 ≤ p.valuation f
  · have hq := hreg.mp hp
    rw [placePoint_eq_zero f hf p hp, placePoint_eq_zero f hf q hq] at h
    have hc := (zeroChartInclusion f hf).injective h
    exact regular_center_injective f hf p q hp hq (congrArg PrimeSpectrum.asIdeal hc)
  · have hq : ¬ 0 ≤ q.valuation f := fun hq => hp (hreg.mpr hq)
    have hip := (inverse_positive_of_not_regular p f hf.ne_zero hp).le
    have hiq := (inverse_positive_of_not_regular q f hf.ne_zero hq).le
    rw [placePoint_eq_infinity f hf p hip, placePoint_eq_infinity f hf q hiq] at h
    have hc := (infinityChartInclusion f hf).injective h
    let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    exact regular_center_injective f⁻¹ (transcendental_inverse f hf) p q hip hiq
      (congrArg PrimeSpectrum.asIdeal hc)

theorem exists_placePoint_eq
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    ∃ p : NormalizedPlace F E, placePoint f hf p = x := by
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq : q.asIdeal ≠ ⊥ := by
      intro h
      have heq : q = genericPoint (Spec (.of (parameterChart f hf))) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext h
      apply hx
      rw [heq]
      exact genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
    let Q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf) :=
      ⟨q.asIdeal, q.isPrime, hq⟩
    let p := chartPlace f hf Q
    refine ⟨p, ?_⟩
    rw [placePoint_eq_zero f hf p (chartPlace_parameter_nonneg f hf Q)]
    congr 1
    apply PrimeSpectrum.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (chartCenter_chartPlace f hf Q)
  · let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    have hq : q.asIdeal ≠ ⊥ := by
      intro h
      have heq : q = genericPoint
          (Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext h
      apply hx
      rw [heq]
      exact genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)
    let Q : IsDedekindDomain.HeightOneSpectrum
        (parameterChart f⁻¹ (transcendental_inverse f hf)) := ⟨q.asIdeal, q.isPrime, hq⟩
    let p := chartPlace f⁻¹ (transcendental_inverse f hf) Q
    refine ⟨p, ?_⟩
    rw [placePoint_eq_infinity f hf p
      (chartPlace_parameter_nonneg f⁻¹ (transcendental_inverse f hf) Q)]
    congr 1
    apply PrimeSpectrum.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (chartCenter_chartPlace f⁻¹ (transcendental_inverse f hf) Q)

def placesEquivNongenericPoints
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    NormalizedPlace F E ≃ {x : parameterCurve f hf // x ≠ genericPoint (parameterCurve f hf)} :=
  Equiv.ofBijective (fun p => ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩) ⟨
    fun _ _ h => placePoint_injective f hf (congrArg Subtype.val h),
    fun x => by
      obtain ⟨p, hp⟩ := exists_placePoint_eq f hf x.1 x.2
      exact ⟨p, Subtype.ext hp⟩⟩

def placesEquivClosedPoints
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    NormalizedPlace F E ≃ {x : parameterCurve f hf // IsClosed ({x} : Set (parameterCurve f hf))} :=
  (placesEquivNongenericPoints f hf).trans
    { toFun := fun x => ⟨x.1, (parameterCurve_isClosed_iff_ne_generic f hf x.1).mpr x.2⟩
      invFun := fun x => ⟨x.1, (parameterCurve_isClosed_iff_ne_generic f hf x.1).mp x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end PiExponent.CurveModelPlaces

end

end OAI
