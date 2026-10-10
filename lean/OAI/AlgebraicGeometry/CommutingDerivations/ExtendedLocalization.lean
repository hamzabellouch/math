import OAI.AlgebraicGeometry.CommutingDerivations.LocalizationEquivalence
import OAI.AlgebraicGeometry.AbhyankarSathaye.Stabilization
import Mathlib.RingTheory.MvPolynomial.Localization

namespace OAI

/-!
Localization coordinates in every dimension `n ≥ 4`.

The localization at `extendedF hn + 1` is a polynomial extension of the
four-dimensional localization, with an explicit structural map from the ambient ring.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

abbrev ExtendedLocalizedAmbient (n : ℕ) := MvPolynomial (Fin (n-4)) LocalizedAmbient

def extendedLocAlgHom {n : ℕ} (hn : 4 ≤ n) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] ExtendedLocalizedAmbient n :=
  (MvPolynomial.mapAlgHom (σ := Fin (n-4))
    (IsScalarTower.toAlgHom ℂ R LocalizedAmbient)).comp (splitAmbient hn).toAlgHom

def extendedLocMap {n : ℕ} (hn : 4 ≤ n) :
    MvPolynomial (Fin n) ℂ →+* ExtendedLocalizedAmbient n :=
  (extendedLocAlgHom hn).toRingHom

@[instance_reducible]
def extendedAlgebra {n : ℕ} (hn : 4 ≤ n) :
    Algebra (MvPolynomial (Fin n) ℂ) (ExtendedLocalizedAmbient n) :=
  (extendedLocMap hn).toAlgebra

theorem extendedScalarTower {n : ℕ} (hn : 4 ≤ n) :
    letI := extendedAlgebra hn
    IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) (ExtendedLocalizedAmbient n) :=
  IsScalarTower.of_algHom (extendedLocAlgHom hn)

@[simp] theorem extendedLocMap_c {n : ℕ} (hn : 4 ≤ n) :
    extendedLocMap hn (extendedF hn+1) = C (loc ambientC) := by
  simp [extendedLocMap, extendedLocAlgHom, splitAmbient_F, ambientC, loc]
  change MvPolynomial.map (algebraMap R LocalizedAmbient) (C F) =
    C ((algebraMap R LocalizedAmbient) F)
  exact map_C _ _

/-- This polynomial extension is the localization of the exact full ambient
ring at the powers of extendedF+1, with the displayed structural map. -/
theorem extended_isLocalization {n : ℕ} (hn : 4 ≤ n) :
    letI := extendedAlgebra hn
    IsLocalization.Away (extendedF hn+1) (ExtendedLocalizedAmbient n) := by
  let := extendedAlgebra hn
  let : Algebra (MvPolynomial (Fin (n-4)) R) (ExtendedLocalizedAmbient n) :=
    MvPolynomial.algebraMvPolynomial
  have : IsLocalization ((Submonoid.powers ambientC).map
      (C : R →+* MvPolynomial (Fin (n-4)) R)) (ExtendedLocalizedAmbient n) :=
    MvPolynomial.isLocalization _ _
  apply IsLocalization.of_ringEquiv_left (splitAmbient hn).toRingEquiv
    (M₁ := (Submonoid.powers ambientC).map (C : R →+* MvPolynomial (Fin (n-4)) R))
  · simp [Submonoid.map_powers, splitAmbient_F, ambientC]
  · intro f
    rfl

def extendedCoefficientMap (n : ℕ) : LaurentCoefficients →+* ExtendedLocalizedAmbient n :=
  C.comp coefficientMap

/-- Complex-linear localization coordinates, with exactly n−1 independent
polynomial variables and the original Laurent coefficient ring. -/
def extendedLocalizationEquiv {n : ℕ} (hn : 4 ≤ n) :
    ExtendedLocalizedAmbient n ≃ₐ[ℂ] MvPolynomial (Fin (n-1)) LaurentCoefficients :=
  (MvPolynomial.mapAlgEquiv (Fin (n-4)) localizationComplexEquiv).trans
    (((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm.restrictScalars ℂ).trans
      ((renameEquiv LaurentCoefficients (blocksToOutput hn)).restrictScalars ℂ))

@[simp] theorem extendedLocalizationEquiv_coefficient {n : ℕ} (hn : 4 ≤ n)
    (a : LaurentCoefficients) :
    extendedLocalizationEquiv hn (extendedCoefficientMap n a) = C a := by
  have ha : localizationComplexEquiv (coefficientMap a) = C a :=
    relativeForward_coefficient a
  change rename (blocksToOutput hn)
    ((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm
      (MvPolynomial.map localizationComplexEquiv (C (coefficientMap a)))) = C a
  rw [map_C]
  change rename (blocksToOutput hn)
    ((sumAlgEquiv LaurentCoefficients (Fin (n-4)) (Fin 3)).symm
      (C (localizationComplexEquiv (coefficientMap a)))) = C a
  rw [ha, sumAlgEquiv_symm_C_C, rename_C]

@[simp] theorem extendedLocalizationEquiv_c {n : ℕ} (hn : 4 ≤ n) :
    extendedLocalizationEquiv hn (extendedLocMap hn (extendedF hn+1)) = C coefficientC := by
  rw [extendedLocMap_c, ← coefficientMap_C]
  exact extendedLocalizationEquiv_coefficient hn coefficientC

@[instance_reducible]
def extendedRelativeAlgebra (n : ℕ) :
    Algebra LaurentCoefficients (ExtendedLocalizedAmbient n) :=
  (extendedCoefficientMap n).toAlgebra

/-- The all-dimensional equivalence fixes precisely the specified Laurent
coefficient map, as an actual relative algebra equivalence. -/
def extendedRelativeLocalizationEquiv {n : ℕ} (hn : 4 ≤ n) :
    letI := extendedRelativeAlgebra n
    ExtendedLocalizedAmbient n ≃ₐ[LaurentCoefficients]
      MvPolynomial (Fin (n-1)) LaurentCoefficients :=
  letI := extendedRelativeAlgebra n
  { (extendedLocalizationEquiv hn).toRingEquiv with
    commutes' := extendedLocalizationEquiv_coefficient hn }

end AbhyankarSathaye.CommutingDerivations

end

end OAI
