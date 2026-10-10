import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalComplex
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalCoordinates

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial
open Ostmann.Arithmetic.PolynomialFlagReplacementFinite
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

theorem erased_dvd_iff_not_isCoprime (i : ι) (P : MvPolynomial ι ℤ)
    (x : Other i → ℤ) (p : ℕ) (hp : p.Prime) (D y : ℤ)
    (hclear : D*y=eval (insertCoordinate i x (p:ℤ)) P)
    (hden : IsCoprime (p:ℤ) D) :
    (p:ℤ) ∣ eval x (eraseCoordinate i P) ↔ ¬IsCoprime (p:ℤ) y := by
  have hpZ : Prime (p:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  rw [← hpZ.irreducible.dvd_iff_not_isCoprime, dvd_eval_eraseCoordinate_iff,← hclear]
  exact ⟨hden.dvd_of_dvd_mul_left,fun h => dvd_mul_of_dvd_right h D⟩

def coprimeSupportedValue (mask : Bool) (p : ℕ) (y : ℤ) (f : ℂ) : ℂ :=
  if mask then if IsCoprime (p:ℤ) y then f else 0 else 0

def polynomialEnlargedValue {κ : Type*} (P : MvPolynomial κ ℤ) (mask : Bool) (f : ℂ) : ℂ :=
  if P=0 then 0 else if mask then f else 0

theorem coprime_enlargement_pointwise (i : ι) (P : MvPolynomial ι ℤ)
    (x : Other i → ℤ) (p : ℕ) (hp : p.Prime) (D y : ℤ) (mask : Bool) (f : ℂ)
    {A : ℝ} (hf : ‖f‖ ≤ A)
    (hclear : mask=true → D*y=eval (insertCoordinate i x (p:ℤ)) P)
    (hden : mask=true → IsCoprime (p:ℤ) D) :
    ‖coprimeSupportedValue mask p y f - polynomialEnlargedValue (eraseCoordinate i P) mask f‖ ≤
      if mask then A*flagError (eraseCoordinate i P) x p else 0 := by
  cases mask with
  | false => simp [coprimeSupportedValue,polynomialEnlargedValue]
  | true =>
    have hiff := erased_dvd_iff_not_isCoprime i P x p hp D y (hclear rfl) (hden rfl)
    by_cases hP : eraseCoordinate i P=0
    · have hnc : ¬IsCoprime (p:ℤ) y := hiff.mp (by simp [hP])
      simp [coprimeSupportedValue,polynomialEnlargedValue,hP,hnc]
    · by_cases hc : IsCoprime (p:ℤ) y
      · have hd : ¬(p:ℤ) ∣ eval x (eraseCoordinate i P) := fun h => hiff.mp h hc
        simp [coprimeSupportedValue,polynomialEnlargedValue,hP,hc,flagError,divisibilityIndicator,hd]
      · have hd := hiff.mpr hc
        simpa [coprimeSupportedValue,polynomialEnlargedValue,hP,hc,flagError,divisibilityIndicator,hd] using hf

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
