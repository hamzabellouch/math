import OAI.AlgebraicGeometry.CommutingDerivations.ExtendedLocalization
import OAI.AlgebraicGeometry.CommutingDerivations.ConcreteKernelIntersection

namespace OAI

/-!
The coefficient algebra of the localization intersects the full ambient
ring in exactly `ℂ[Fₙ]` in every dimension `n ≥ 4`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

@[simp] theorem extendedCoefficientMap_complex (n : ℕ) (a : ℂ) :
    extendedCoefficientMap n (algebraMap ℂ LaurentCoefficients a) =
      algebraMap ℂ (ExtendedLocalizedAmbient n) a := by
  change C (coefficientMap (algebraMap ℂ LaurentCoefficients a)) = _
  rw [coefficientMap_complex_intersection]
  rfl

theorem extendedCoefficientMap_polynomial {n : ℕ} (hn : 4 ≤ n) (q : Polynomial ℂ) :
    extendedCoefficientMap n (algebraMap (Polynomial ℂ) LaurentCoefficients q) =
      extendedLocMap hn (Polynomial.aeval (extendedAmbientParameter hn) q) := by
  change C (coefficientMap (algebraMap (Polynomial ℂ) LaurentCoefficients q)) = _
  rw [coefficientMap_polynomial]
  let original : R →ₐ[ℂ] ExtendedLocalizedAmbient n :=
    (IsScalarTower.toAlgHom ℂ LocalizedAmbient (ExtendedLocalizedAmbient n)).comp
      (IsScalarTower.toAlgHom ℂ R LocalizedAmbient)
  have he : original.comp (Polynomial.aeval ambientC) =
      (extendedLocAlgHom hn).comp (Polynomial.aeval (extendedAmbientParameter hn)) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X]
    change C (loc ambientC) = extendedLocMap hn (extendedF hn + 1)
    exact (extendedLocMap_c hn).symm
  exact AlgHom.congr_fun he q

theorem extendedCoefficientMap_parameter {n : ℕ} (hn : 4 ≤ n) :
    extendedCoefficientMap n coefficientC = extendedLocMap hn (extendedAmbientParameter hn) := by
  change C (coefficientMap coefficientC) = extendedLocMap hn (extendedF hn + 1)
  rw [coefficientMap_C, extendedLocMap_c]

/-- Exact input to the generic commuting-family construction, specialized to
the actual all-dimensional localization and coordinate equivalence. -/
theorem extended_localization_kernel_intersection {n : ℕ} (hn : 4 ≤ n)
    (r : MvPolynomial (Fin n) ℂ) :
    (∃ b : LaurentCoefficients,
      extendedLocalizationEquiv hn (extendedLocMap hn r) = C b) ↔
    r ∈ Algebra.adjoin ℂ ({extendedF hn} : Set (MvPolynomial (Fin n) ℂ)) := by
  let := extendedAlgebra hn
  let : IsLocalization.Away (extendedAmbientParameter hn) (ExtendedLocalizedAmbient n) := by
    change IsLocalization.Away (extendedF hn + 1) (ExtendedLocalizedAmbient n)
    exact extended_isLocalization hn
  constructor
  · rintro ⟨b, hb⟩
    have hpre : extendedLocMap hn r = extendedCoefficientMap n b := by
      apply (extendedLocalizationEquiv hn).injective
      rw [hb, extendedLocalizationEquiv_coefficient]
    obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial ℂ) b
    change b * coefficientC^m = algebraMap (Polynomial ℂ) LaurentCoefficients q at hq
    have he : extendedCoefficientMap n b *
        (extendedLocMap hn (extendedAmbientParameter hn))^m =
        extendedLocMap hn (Polynomial.aeval (extendedAmbientParameter hn) q) := by
      simpa only [map_mul, map_pow, extendedCoefficientMap_parameter hn,
        extendedCoefficientMap_polynomial hn] using congrArg (extendedCoefficientMap n) hq
    apply (extendedParameter_laurent_intersection hn (ExtendedLocalizedAmbient n) r).mp
    refine ⟨m, q, ?_⟩
    change (extendedLocMap hn (extendedAmbientParameter hn))^m * extendedLocMap hn r =
      extendedLocMap hn (Polynomial.aeval (extendedAmbientParameter hn) q)
    rw [hpre, mul_comm]
    exact he
  · intro hr
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨q, hq⟩ := hr
    obtain ⟨p, hp⟩ := (exists_aeval_add_one_iff (K := ℂ) (extendedF hn) r).mpr ⟨q, hq.symm⟩
    refine ⟨algebraMap (Polynomial ℂ) LaurentCoefficients p, ?_⟩
    calc
      extendedLocalizationEquiv hn (extendedLocMap hn r) =
          extendedLocalizationEquiv hn
            (extendedCoefficientMap n (algebraMap (Polynomial ℂ) LaurentCoefficients p)) := by
        apply congrArg (extendedLocalizationEquiv hn)
        rw [extendedCoefficientMap_polynomial]
        exact congrArg (extendedLocMap hn) hp
      _ = C (algebraMap (Polynomial ℂ) LaurentCoefficients p) :=
        extendedLocalizationEquiv_coefficient hn _

end AbhyankarSathaye.CommutingDerivations

end

end OAI
