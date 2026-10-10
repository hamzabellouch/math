import OAI.AlgebraicGeometry.CommutingDerivations.LocalizationSetup
import OAI.AlgebraicGeometry.CommutingDerivations.ExtendedParameterRetraction

namespace OAI

/-!
The Laurent coefficient-map image intersects the ambient ring in exactly
`ℂ[F]`, by the explicit parameter retraction.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations

theorem polynomialCoefficientMap_apply (q : Polynomial ℂ) :
    polynomialCoefficientMap q = loc (Polynomial.aeval ambientC q) := by
  have he := Polynomial.aeval_algHom
    (IsScalarTower.toAlgHom ℂ R LocalizedAmbient) ambientC
  exact AlgHom.congr_fun he q

@[simp] theorem coefficientMap_polynomial (q : Polynomial ℂ) :
    coefficientMap (algebraMap (Polynomial ℂ) LaurentCoefficients q) =
      loc (Polynomial.aeval ambientC q) := by
  rw [← polynomialCoefficientMap_apply]
  unfold coefficientMap
  exact IsLocalization.Away.lift_eq _ _ _

/-- Constants in the actual Laurent coefficient algebra have the prescribed
complex scalar image in the actual ambient localization. -/
@[simp] theorem coefficientMap_complex_intersection (a : ℂ) :
    coefficientMap (algebraMap ℂ LaurentCoefficients a) = algebraMap ℂ LocalizedAmbient a := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) LaurentCoefficients]
  rw [coefficientMap_polynomial]
  simp [loc, IsScalarTower.algebraMap_apply ℂ R LocalizedAmbient]

/-- Literal common-kernel intersection form: membership in the image of the
actual coefficient map is equivalent to an ordinary polynomial in F. -/
theorem coefficientMap_intersection (r : R) :
    (∃ a : LaurentCoefficients, loc r = coefficientMap a) ↔
      ∃ q : Polynomial ℂ, r = Polynomial.aeval F q := by
  let : IsLocalization.Away ambientParameter LocalizedAmbient := by
    change IsLocalization.Away ambientC LocalizedAmbient
    infer_instance
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial ℂ) a
    change a * coefficientC^m = algebraMap (Polynomial ℂ) LaurentCoefficients q at hq
    have he : coefficientMap a * (loc ambientC)^m = loc (Polynomial.aeval ambientC q) := by
      simpa only [map_mul, map_pow, coefficientMap_C, coefficientMap_polynomial] using
        congrArg coefficientMap hq
    have hpoly : ∃ q : Polynomial ℂ, r = Polynomial.aeval ambientParameter q := by
      apply (parameter_laurent_intersection LocalizedAmbient r).mp
      refine ⟨m, q, ?_⟩
      change (loc ambientC)^m * loc r = loc (Polynomial.aeval ambientC q)
      rw [ha, mul_comm]
      exact he
    exact (exists_aeval_add_one_iff (K := ℂ) F r).mp hpoly
  · intro hr
    obtain ⟨q, hq⟩ := (exists_aeval_add_one_iff (K := ℂ) F r).mpr hr
    refine ⟨algebraMap (Polynomial ℂ) LaurentCoefficients q, ?_⟩
    rw [coefficientMap_polynomial]
    exact congrArg loc hq

theorem coefficientMap_intersection_adjoin (r : R) :
    (∃ a : LaurentCoefficients, loc r = coefficientMap a) ↔
      r ∈ Algebra.adjoin ℂ ({F} : Set R) := by
  rw [coefficientMap_intersection, Algebra.adjoin_singleton_eq_range_aeval]
  change (∃ q : Polynomial ℂ, r = Polynomial.aeval F q) ↔
    ∃ q : Polynomial ℂ, Polynomial.aeval F q = r
  simp only [eq_comm]

end AbhyankarSathaye.CommutingDerivations

end

end OAI
