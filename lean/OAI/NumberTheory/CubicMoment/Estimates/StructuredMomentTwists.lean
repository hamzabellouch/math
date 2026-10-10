import OAI.NumberTheory.CubicMoment.Estimates.PrimeMomentCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.SmallSecondConductorPowers

namespace OAI

/-! The exact modulus and unit condition for the numerator/exclusion twist. -/
noncomputable section
namespace CubicFirstMoment

def structuredTwistModulus (v e : Eisenstein) : Eisenstein := 1*((9*v)*e)

def structuredTwistCharacter (hpub : CubicSupplementaryPeriodicity)
    (v e : Eisenstein) (hv : v ≠ 0) : MulChar (Residues (structuredTwistModulus v e)) ℂ :=
  productResidueChar (1 : MulChar (Residues (1:Eisenstein)) ℂ)
    (productResidueChar (cubicNumeratorChar hpub v hv) (1 : MulChar (Residues e) ℂ))

lemma structuredTwistModulus_ne_zero {v e : Eisenstein} (hv : v ≠ 0) (he : e ≠ 0) :
    structuredTwistModulus v e ≠ 0 := by
  exact mul_ne_zero one_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hv) he)

lemma structuredTwistCharacter_units (hpub : CubicSupplementaryPeriodicity)
    (v e : Eisenstein) (hv : v ≠ 0) (u : Eisensteinˣ) :
    structuredTwistCharacter hpub v e hv
      (Ideal.Quotient.mk (modulus (structuredTwistModulus v e)) u) = 1 := by
  apply productResidueChar_units
  · intro w
    exact MulChar.one_apply (w.isUnit.map (Ideal.Quotient.mk (modulus (1:Eisenstein))))
  · intro w
    apply productResidueChar_units
    · exact cubicNumeratorChar_units hpub v hv
    · intro w
      exact MulChar.one_apply (w.isUnit.map (Ideal.Quotient.mk (modulus e)))

lemma structuredTwistModulus_bound {Y δ d : ℝ} (hY : 1 ≤ Y) (hd : 3*δ ≤ d)
    (h81 : 81 ≤ Y^δ) {v e : Eisenstein} (hv : norm v ≤ Y^δ) (he : norm e ≤ Y^δ) :
    norm (structuredTwistModulus v e) ≤ Y^d := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have h9 : norm (9:Eisenstein) = 81 := by
    change Complex.normSq (9:ℂ) = 81
    norm_num
  calc
    norm (structuredTwistModulus v e) = 81*(norm v*norm e) := by
      simp only [structuredTwistModulus,one_mul,norm_mul_eq,h9]
      ring
    _ ≤ 81*(Y^δ*Y^δ) := by gcongr; exact norm_nonneg e
    _ ≤ Y^δ*(Y^δ*Y^δ) := by gcongr
    _ = Y^(3*δ) := by rw [← Real.rpow_add hYp,← Real.rpow_add hYp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hd

end CubicFirstMoment

end

end OAI
