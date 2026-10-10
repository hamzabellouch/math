import OAI.AlgebraicGeometry.CommutingDerivations.ParameterBezout
import OAI.AlgebraicGeometry.AbhyankarSathaye.Reconstruction
import OAI.AlgebraicGeometry.AbhyankarSathaye.Quotient
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Fin.VecNotation

namespace OAI

/-!
The Laurent coefficient algebra and localization coordinates.
The coefficient map is the lift of `t ↦ F + 1`.
-/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

def ambientC : R := F + 1
abbrev LocalizedAmbient := Localization.Away ambientC
abbrev LaurentCoefficients := Localization.Away (Polynomial.X : Polynomial ℂ)
abbrev RelativePlane := MvPolynomial (Fin 3) LaurentCoefficients

def loc : R →+* LocalizedAmbient := algebraMap R LocalizedAmbient
def coefficientC : LaurentCoefficients :=
  algebraMap (Polynomial ℂ) LaurentCoefficients Polynomial.X
def coefficientD : LaurentCoefficients :=
  IsLocalization.Away.invSelf (Polynomial.X : Polynomial ℂ)
def localD : LocalizedAmbient := IsLocalization.Away.invSelf ambientC

theorem coefficient_unit : coefficientC * coefficientD = 1 :=
  IsLocalization.Away.mul_invSelf _

theorem local_unit : loc ambientC * localD = 1 :=
  IsLocalization.Away.mul_invSelf _

def polynomialCoefficientMap : Polynomial ℂ →+* LocalizedAmbient :=
  (Polynomial.aeval (loc ambientC)).toRingHom

def coefficientMap : LaurentCoefficients →+* LocalizedAmbient :=
  IsLocalization.Away.lift Polynomial.X
    (by
      refine ⟨⟨polynomialCoefficientMap Polynomial.X, localD, ?_, ?_⟩, rfl⟩
      · simpa [polynomialCoefficientMap] using local_unit
      · simpa [polynomialCoefficientMap, mul_comm] using local_unit)

@[simp] theorem coefficientMap_C : coefficientMap coefficientC = loc ambientC := by
  simp [coefficientMap, coefficientC, polynomialCoefficientMap]

@[simp] theorem coefficientMap_D : coefficientMap coefficientD = localD := by
  have h1 : loc ambientC * coefficientMap coefficientD = 1 := by
    simpa using congrArg coefficientMap coefficient_unit
  calc
    coefficientMap coefficientD = (loc ambientC * localD) * coefficientMap coefficientD := by
      rw [local_unit, one_mul]
    _ = localD * (loc ambientC * coefficientMap coefficientD) := by ring
    _ = localD := by rw [h1, mul_one]

def localAlpha : LocalizedAmbient := localD^2 * parameterA (loc ambientC) (loc x) (loc s)
def localBeta : LocalizedAmbient :=
  localD^2 * parameterB (loc ambientC) (loc x) (loc y) (loc s)
def localT : LocalizedAmbient := parameter localAlpha localBeta (loc u) (loc v) (loc w)
def localCoordinates : Fin 3 → LocalizedAmbient := ![loc shiftX, loc shiftY, localT]

theorem local_cusp : (loc x)^2 + (loc y)^3 = loc s * loc h := by
  simpa [mul_comm] using congrArg loc cusp

theorem local_section : loc h = loc ambientC + P (loc x) (loc y) (loc s) := by
  have he : h = ambientC + P x y s := by unfold ambientC F p; ring
  simpa using congrArg loc he

theorem local_bezout : localAlpha * loc h + localBeta * loc y = 1 :=
  parameter_bezout_unit _ _ _ _ _ _ local_cusp local_section local_unit

theorem local_recover_s : localD * ((loc shiftX)^2 + (loc shiftY)^3) = loc s := by
  simpa [shiftX, shiftY] using
    parameter_recover_s _ _ _ _ _ _ local_cusp local_section local_unit

/-- Evaluation at the displayed X,Y,T, with the explicit relative coefficient map. -/
def relativeBackward : RelativePlane →+* LocalizedAmbient :=
  eval₂Hom coefficientMap localCoordinates

@[simp] theorem relativeBackward_C (a : LaurentCoefficients) :
    relativeBackward (C a) = coefficientMap a := by
  simp [relativeBackward]

@[simp] theorem relativeBackward_X (i : Fin 3) :
    relativeBackward (X i) = localCoordinates i := by
  simp [relativeBackward]

/-- A relative algebra equivalence over `ℂ[c,c⁻¹]`, with `c = F + 1`,
and its coordinate equations. -/
def RelativeLocalizationContract : Prop :=
  ∃ e : LocalizedAmbient ≃+* RelativePlane,
    (∀ a, e (coefficientMap a) = C a) ∧
    e (loc shiftX) = X 0 ∧ e (loc shiftY) = X 1 ∧ e localT = X 2 ∧
    e.symm.toRingHom = relativeBackward

end AbhyankarSathaye.CommutingDerivations

end

end OAI
