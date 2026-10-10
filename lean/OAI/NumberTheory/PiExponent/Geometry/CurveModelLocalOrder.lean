import OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveModelLocalOrder
universe u
open CurveZeroPole CurveValuationCenter WeightedCurveDegree
open CurveNormalizationModel CurveModelPlaces
open AlgebraicGeometry CategoryTheory

def chartCenterLocalRingEquiv
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp) ≃+*
      PlaceValuationRing.ring p := by
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
  let φ := parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp
  have he : p.valuation = CurveLocalOrder.fractionAddValuation A E :=
    valuation_eq_chartCenter f hf p hp
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
    exact (parameterCenterLocalHom_coe f hf p.valuation p.constants_nonneg hp a).trans ha

def chartCenterLocalAlgEquiv
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    letI := ParameterResidueField.parameterChartConstants f hf
    Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp) ≃ₐ[F]
      PlaceValuationRing.ring p := by
  let := ParameterResidueField.parameterChartConstants f hf
  refine { chartCenterLocalRingEquiv f hf p hp with commutes' := ?_ }
  intro c
  apply Subtype.ext
  change (parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp
    (algebraMap F _ c) : E) = algebraMap F E c
  rw [IsScalarTower.algebraMap_apply F (parameterChart f hf)
    (Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp))]
  rw [parameterCenterLocalHom_algebraMap]
  let := parameterPolynomialAlgebra f hf
  change (algebraMap F[X] E (Polynomial.C c)) = algebraMap F E c
  rw [parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]

def placePointStalkRingEquiv
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) :
    (parameterCurve f hf).presheaf.stalk (placePoint f hf p) ≃+*
      PlaceValuationRing.ring p := by
  by_cases hp : 0 ≤ p.valuation f
  · rw [placePoint_eq_zero f hf p hp]
    exact (zeroChartStalkIso f hf _).commRingCatIsoToRingEquiv.trans
      (chartCenterLocalRingEquiv f hf p hp)
  · letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    have hi := (inverse_positive_of_not_regular p f hf.ne_zero hp).le
    rw [placePoint_eq_infinity f hf p hi]
    exact (infinityChartStalkIso f hf _).commRingCatIsoToRingEquiv.trans
      (chartCenterLocalRingEquiv f⁻¹ (transcendental_inverse f hf) p hi)

theorem addVal_ringEquiv
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (e : A ≃+* B) (a : A) :
    IsDiscreteValuationRing.addVal B (e a) = IsDiscreteValuationRing.addVal A a := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_prime A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ.irreducible
  rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_def' u hπ.irreducible n]
  exact IsDiscreteValuationRing.addVal_def' (Units.map e.toMonoidHom u)
    (hπ.irreducible.map e) n

theorem placePointStalkRingEquiv_addVal
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E)
    (a : (parameterCurve f hf).presheaf.stalk (placePoint f hf p)) :
    letI := parameterCurve_stalkDVR f hf (placePoint f hf p) (placePoint_ne_genericPoint f hf p)
    IsDiscreteValuationRing.addVal (PlaceValuationRing.ring p)
      (placePointStalkRingEquiv f hf p a) =
    IsDiscreteValuationRing.addVal ((parameterCurve f hf).presheaf.stalk (placePoint f hf p)) a := by
  let := parameterCurve_stalkDVR f hf (placePoint f hf p) (placePoint_ne_genericPoint f hf p)
  exact addVal_ringEquiv (placePointStalkRingEquiv f hf p) a

theorem placePoint_valuation_stalk
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E)
    (a : (parameterCurve f hf).presheaf.stalk (placePoint f hf p)) :
    letI := parameterCurve_stalkDVR f hf (placePoint f hf p) (placePoint_ne_genericPoint f hf p)
    p.valuation ((placePointStalkRingEquiv f hf p a : PlaceValuationRing.ring p) : E) =
      CurveLocalOrder.enatToIntegerOrder
        (IsDiscreteValuationRing.addVal
          ((parameterCurve f hf).presheaf.stalk (placePoint f hf p)) a) := by
  let := parameterCurve_stalkDVR f hf (placePoint f hf p) (placePoint_ne_genericPoint f hf p)
  rw [PlaceValuationRing.valuation_eq_fractionAddValuation p]
  change CurveLocalOrder.fractionAddValuation (PlaceValuationRing.ring p) E
    (algebraMap (PlaceValuationRing.ring p) E (placePointStalkRingEquiv f hf p a)) = _
  rw [CurveLocalOrder.fractionAddValuation_algebraMap, CurveLocalOrder.localAddValuation_apply,
    placePointStalkRingEquiv_addVal]

theorem placePoint_valuation_eq_colength
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E)
    (a : (parameterCurve f hf).presheaf.stalk (placePoint f hf p)) (ha : a ≠ 0) :
    p.valuation ((placePointStalkRingEquiv f hf p a : PlaceValuationRing.ring p) : E) =
      CurveLocalOrder.enatToIntegerOrder
        (Module.length ((parameterCurve f hf).presheaf.stalk (placePoint f hf p))
          (((parameterCurve f hf).presheaf.stalk (placePoint f hf p)) ⧸ Ideal.span {a})) := by
  let := parameterCurve_stalkDVR f hf (placePoint f hf p) (placePoint_ne_genericPoint f hf p)
  simpa only [CurveLocalOrder.length_quotient_span_eq_addVal ha]
    using placePoint_valuation_stalk f hf p a

end PiExponent.CurveModelLocalOrder

end

end OAI
