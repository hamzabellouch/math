import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Normalization
import OAI.NumberTheory.PiExponent.Geometry.CurveZeroPole

namespace OAI

noncomputable section

namespace PiExponent.CurveNormalizationModel

open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole

def integralClosureTowerHom
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E] :
    integralClosure R E →+* integralClosure S E where
  toFun x := ⟨x.1, x.2.tower_top⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem integralClosureTower_isLocalizationAway
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R E r) E] :
    letI : Algebra (integralClosure R E) (integralClosure S E) :=
      integralClosureTowerHom.toAlgebra
    IsLocalization.Away (algebraMap R (integralClosure R E) r) (integralClosure S E) := by
  let : Algebra (integralClosure R E) (integralClosure S E) :=
    integralClosureTowerHom.toAlgebra
  have : IsScalarTower (integralClosure R E) (integralClosure S E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R (integralClosure R E) (integralClosure S E) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact IsLocalization.Away.integralClosure (S := E) (Rf := S) (Sf := E) r

theorem integralClosureTower_SpecMap_isOpenImmersion
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R E r) E] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (integralClosureTowerHom (R := R) (S := S) (E := E)))) := by
  let : Algebra (integralClosure R E) (integralClosure S E) :=
    integralClosureTowerHom.toAlgebra
  have : IsLocalization.Away (algebraMap R (integralClosure R E) r) (integralClosure S E) :=
    integralClosureTower_isLocalizationAway r
  exact IsOpenImmersion.of_isLocalization (algebraMap R (integralClosure R E) r)

def parameterLaurentMap {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : LaurentPolynomial F →+* E :=
  LaurentPolynomial.eval₂ (algebraMap F E) (Units.mk0 f hf.ne_zero)

abbrev parameterLaurentAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra (LaurentPolynomial F) E :=
  (parameterLaurentMap f hf).toAlgebra

@[simp]
theorem parameterLaurentMap_T {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentMap f hf (LaurentPolynomial.T 1) = f := by
  simp [parameterLaurentMap, LaurentPolynomial.eval₂_T]

@[simp]
theorem parameterLaurentMap_T_inv {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentMap f hf (LaurentPolynomial.T (-1)) = f⁻¹ := by
  simp [parameterLaurentMap, LaurentPolynomial.eval₂_T]

theorem parameterLaurent_scalarTower {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    letI := parameterPolynomialAlgebra f hf
    letI := parameterLaurentAlgebra f hf
    IsScalarTower F[X] (LaurentPolynomial F) E := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  apply IsScalarTower.of_algebraMap_eq
  intro p
  rw [parameterPolynomialAlgebra_map]
  change Polynomial.aeval f p = parameterLaurentMap f hf (Polynomial.toLaurent p)
  rw [parameterLaurentMap, LaurentPolynomial.eval₂_toLaurent]
  rfl

abbrev parameterLaurentChart {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterLaurentAlgebra f hf
  integralClosure (LaurentPolynomial F) E

def parameterChartOverlapHom {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterChart f hf →+* parameterLaurentChart f hf := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  exact integralClosureTowerHom

theorem parameterChartOverlap_isOpenImmersion
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f hf))) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  have hunit : IsLocalization.Away f E := IsLocalization.of_le_isUnit (by
    rintro x ⟨n, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hf.ne_zero).pow n)
  have hX : algebraMap F[X] E Polynomial.X = f := by
    rw [parameterPolynomialAlgebra_map]
    simp
  have : IsLocalization.Away (algebraMap F[X] E Polynomial.X) E := by
    simpa only [hX] using hunit
  exact integralClosureTower_SpecMap_isOpenImmersion (S := LaurentPolynomial F) (E := E)
    (Polynomial.X : F[X])

theorem parameterLaurentMap_invert
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    (parameterLaurentMap f hf).comp (LaurentPolynomial.invert (R := F)).toRingHom =
      parameterLaurentMap f⁻¹ (transcendental_inverse f hf) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : F[X]))
  apply Polynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      parameterLaurentMap, LaurentPolynomial.eval₂_C]
  · simp [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent]

theorem isIntegralElem_comp_equiv
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    (g : S →+* E) (e : R ≃+* S) (x : E) :
    (g.comp e.toRingHom).IsIntegralElem x ↔ g.IsIntegralElem x := by
  constructor
  · exact RingHom.isIntegralElem.of_comp e.toRingHom g
  · intro hx
    apply RingHom.isIntegralElem.of_comp e.symm.toRingHom (g.comp e.toRingHom)
    have heq : (g.comp e.toRingHom).comp e.symm.toRingHom = g := by ext; simp
    rwa [heq]

def reciprocalLaurentChartEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentChart f hf ≃+*
      parameterLaurentChart f⁻¹ (transcendental_inverse f hf) where
  toFun x := ⟨x.1, by
    have hx := (isIntegralElem_comp_equiv (parameterLaurentMap f hf)
      (LaurentPolynomial.invert (R := F)).toRingEquiv x.1).mpr x.2
    rw [parameterLaurentMap_invert] at hx
    exact hx⟩
  invFun x := ⟨x.1, by
    apply (isIntegralElem_comp_equiv (parameterLaurentMap f hf)
      (LaurentPolynomial.invert (R := F)).toRingEquiv x.1).mp
    rw [parameterLaurentMap_invert]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def zeroOverlap : Spec (.of (parameterLaurentChart f hf)) ⟶ Spec (.of (parameterChart f hf)) :=
  Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f hf))

instance zeroOverlap_isOpenImmersion : IsOpenImmersion (zeroOverlap f hf) :=
  parameterChartOverlap_isOpenImmersion f hf

def infinityOverlap : Spec (.of (parameterLaurentChart f hf)) ⟶
    Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) :=
  Spec.map (CommRingCat.ofHom ((reciprocalLaurentChartEquiv f hf).symm.toRingHom.comp
    (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf))))

instance infinityOverlap_isOpenImmersion : IsOpenImmersion (infinityOverlap f hf) := by
  let e := (reciprocalLaurentChartEquiv f hf).symm
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toCommRingCatIso.hom)
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf)))) :=
    parameterChartOverlap_isOpenImmersion f⁻¹ (transcendental_inverse f hf)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf)))))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

def parameterCurve : Scheme :=
  Limits.pushout (zeroOverlap f hf) (infinityOverlap f hf)

def zeroChartInclusion : Spec (.of (parameterChart f hf)) ⟶ parameterCurve f hf :=
  Limits.pushout.inl (zeroOverlap f hf) (infinityOverlap f hf)

def infinityChartInclusion : Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) ⟶
    parameterCurve f hf :=
  Limits.pushout.inr (zeroOverlap f hf) (infinityOverlap f hf)

instance zeroChartInclusion_isOpenImmersion : IsOpenImmersion (zeroChartInclusion f hf) :=
  inferInstanceAs (IsOpenImmersion (Limits.colimit.ι
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) Limits.WalkingSpan.left))

instance infinityChartInclusion_isOpenImmersion : IsOpenImmersion (infinityChartInclusion f hf) :=
  inferInstanceAs (IsOpenImmersion (Limits.colimit.ι
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) Limits.WalkingSpan.right))

theorem parameterCurve_overlap_compatibility :
    zeroOverlap f hf ≫ zeroChartInclusion f hf =
      infinityOverlap f hf ≫ infinityChartInclusion f hf :=
  Limits.pushout.condition

theorem parameterCurve_twoChartCover (x : parameterCurve f hf) :
    (∃ y, zeroChartInclusion f hf y = x) ∨
      ∃ y, infinityChartInclusion f hf y = x := by
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) x
  cases j with
  | none =>
    left
    refine ⟨zeroOverlap f hf y, ?_⟩
    have hh := congrArg (fun g => g y)
      (Limits.colimit.w (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))
        Limits.WalkingSpan.Hom.fst)
    exact hh.trans hy
  | some j =>
    cases j with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

def zeroChartStalkIso (x : PrimeSpectrum (parameterChart f hf)) :
    (parameterCurve f hf).presheaf.stalk (zeroChartInclusion f hf x) ≅
      CommRingCat.of (Localization.AtPrime x.asIdeal) := by
  have : IsIso ((zeroChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (zeroChartInclusion_isOpenImmersion f hf)).2 x
  exact asIso ((zeroChartInclusion f hf).stalkMap x) ≪≫
    Spec.stalkIso (.of (parameterChart f hf)) x

def infinityChartStalkIso
    (x : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf))) :
    (parameterCurve f hf).presheaf.stalk (infinityChartInclusion f hf x) ≅
      CommRingCat.of (Localization.AtPrime x.asIdeal) := by
  have : IsIso ((infinityChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (infinityChartInclusion_isOpenImmersion f hf)).2 x
  exact asIso ((infinityChartInclusion f hf).stalkMap x) ≪≫
    Spec.stalkIso (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) x

instance parameterCurve_compactSpace : CompactSpace (parameterCurve f hf) := by
  rw [← isCompact_univ_iff]
  have hcover : Set.range (zeroChartInclusion f hf) ∪
      Set.range (infinityChartInclusion f hf) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    exact parameterCurve_twoChartCover f hf x
  rw [← hcover]
  exact (isCompact_range (zeroChartInclusion f hf).continuous).union
    (isCompact_range (infinityChartInclusion f hf).continuous)

theorem parameterCurve_genericPoint :
    IsGenericPoint
      (zeroChartInclusion f hf (zeroOverlap f hf
        (genericPoint (Spec (.of (parameterLaurentChart f hf)))))) Set.univ := by
  apply isGenericPoint_iff_specializes.mpr
  intro x
  constructor
  · intro _; trivial
  · intro _
    rcases parameterCurve_twoChartCover f hf x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rw [genericPoint_eq_of_isOpenImmersion (zeroOverlap f hf)]
      exact (genericPoint_specializes y).map (zeroChartInclusion f hf).continuous
    · have he := congrArg
        (fun g => g (genericPoint (Spec (.of (parameterLaurentChart f hf)))))
        (parameterCurve_overlap_compatibility f hf)
      change zeroChartInclusion f hf (zeroOverlap f hf _) =
        infinityChartInclusion f hf (infinityOverlap f hf _) at he
      rw [he, genericPoint_eq_of_isOpenImmersion (infinityOverlap f hf)]
      exact (genericPoint_specializes y).map (infinityChartInclusion f hf).continuous

instance parameterCurve_irreducibleSpace : IrreducibleSpace (parameterCurve f hf) :=
  (irreducibleSpace_def _).mpr (parameterCurve_genericPoint f hf).isIrreducible

instance parameterCurve_isReduced : IsReduced (parameterCurve f hf) := by
  have (x : parameterCurve f hf) : _root_.IsReduced ((parameterCurve f hf).presheaf.stalk x) := by
    rcases parameterCurve_twoChartCover f hf x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact isReduced_of_injective (zeroChartStalkIso f hf y).hom.hom
        (zeroChartStalkIso f hf y).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective (infinityChartStalkIso f hf y).hom.hom
        (infinityChartStalkIso f hf y).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

instance parameterCurve_isIntegral : IsIntegral (parameterCurve f hf) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

def parameterCurveFunctionFieldIso :
    (parameterCurve f hf).functionField ≅ (Spec (.of (parameterChart f hf))).functionField := by
  let x := genericPoint (Spec (.of (parameterChart f hf)))
  have : IsIso ((zeroChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (zeroChartInclusion_isOpenImmersion f hf)).2 x
  have hx : zeroChartInclusion f hf x = genericPoint (parameterCurve f hf) :=
    genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  exact eqToIso (congrArg (fun y => (parameterCurve f hf).presheaf.stalk y) hx.symm) ≪≫
    asIso ((zeroChartInclusion f hf).stalkMap x)

def parameterCurveFunctionFieldEquiv
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (parameterCurve f hf).functionField ≃+* E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  letI : Algebra (parameterChart f hf) (Spec (.of (parameterChart f hf))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (parameterChart f hf))
  letI : IsFractionRing (parameterChart f hf) (Spec (.of (parameterChart f hf))).functionField :=
    functionField_isFractionRing_of_affine (.of (parameterChart f hf))
  exact (parameterCurveFunctionFieldIso f hf).commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (nonZeroDivisors (parameterChart f hf))
      (Spec (.of (parameterChart f hf))).functionField E).toRingEquiv

end PiExponent.CurveNormalizationModel

end

end OAI
