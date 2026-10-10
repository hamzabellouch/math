import OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite
import OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula
import OAI.NumberTheory.PiExponent.Geometry.PlaceValuationRing
import OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterResidueField
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.PlaceParameterModel
open CurveZeroPole CurveValuationCenter WeightedCurveDegree

def parameterUnit {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : Eˣ := Classical.choose p.normalized

theorem parameterUnit_order {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : integerOrder p.valuation (parameterUnit p) = 1 :=
  Classical.choose_spec p.normalized

def parameter {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : E := parameterUnit p

theorem parameter_nonzero {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : parameter p ≠ 0 := (parameterUnit p).ne_zero

theorem parameter_value {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : p.valuation (parameter p) = 1 := by
  have h := coe_integerOrder p.valuation (parameterUnit p)
  rw [parameterUnit_order] at h
  exact h.symm

theorem parameter_positive {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : 0 < p.valuation (parameter p) := by
  rw [parameter_value]
  norm_num

theorem parameter_transcendental
    {F E : Type*} [Field F] [IsAlgClosed F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : Transcendental F (parameter p) := by
  intro ha
  have hm : parameter p ∈ algebraicClosure F E := mem_algebraicClosure_iff.mpr ha
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure F E)] at hm
  obtain ⟨c, hc⟩ := hm
  change algebraMap F E c = parameter p at hc
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact parameter_nonzero p hc.symm
  have hz := CurveProductFormula.valuation_constant_eq_zero p c hc0
  rw [hc, parameter_value] at hz
  exact one_ne_zero hz

def parameterCenterLocalRingEquiv
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 < p.valuation f) :
    Localization.AtPrime (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).1 ≃+*
      p.valuation.toValuation.valuationSubring := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let q := parameterValuationCenter f hf p.valuation p.constants_nonneg hp.le
  have hq : q ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F)
      (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).property
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq A
  let φ := parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp.le
  have he : p.valuation = CurveLocalOrder.fractionAddValuation A E :=
    valuation_eq_parameterPlaceValuation f hf p.valuation p.constants_nonneg hp p.normalized
  apply RingEquiv.ofBijective φ
  constructor
  · intro a b hab
    apply IsFractionRing.injective A E
    have hh := congrArg (fun x : p.valuation.toValuation.valuationSubring => (x : E)) hab
    simpa only [φ, parameterCenterLocalHom_coe] using hh
  · intro x
    have hx : 0 ≤ CurveLocalOrder.fractionAddValuation A E (x : E) := by
      rw [← he]
      exact x.property
    obtain ⟨a, ha⟩ := (WeightedLocalLattice.exists_local_element_iff_nonnegative_order
      (A := A) (x : E)).mpr hx
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact (parameterCenterLocalHom_coe f hf p.valuation p.constants_nonneg hp.le a).trans ha

def parameterCenterLocalAlgEquiv
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 < p.valuation f) :
    letI := ParameterResidueField.parameterChartConstants f hf
    Localization.AtPrime (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).1 ≃ₐ[F]
      PlaceValuationRing.ring p := by
  let := ParameterResidueField.parameterChartConstants f hf
  refine { parameterCenterLocalRingEquiv f hf p hp with commutes' := ?_ }
  intro c
  apply Subtype.ext
  change (parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp.le
    (algebraMap F _ c) : E) = algebraMap F E c
  rw [IsScalarTower.algebraMap_apply F (parameterChart f hf)
    (Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp.le))]
  rw [parameterCenterLocalHom_algebraMap]
  let := parameterPolynomialAlgebra f hf
  change (algebraMap F[X] E (Polynomial.C c)) = algebraMap F E c
  rw [parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]

end PiExponent.PlaceParameterModel

end

end OAI
