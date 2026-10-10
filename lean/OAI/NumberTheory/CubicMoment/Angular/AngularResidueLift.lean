import OAI.NumberTheory.CubicMoment.Angular.AngularSmallPartCharacter
import OAI.NumberTheory.CubicMoment.Estimates.StructuredMomentTwists

namespace OAI

/-! The finite factor above three compensates the fixed infinity type.
It is one on every primary element, so it does not change the original sums. -/
noncomputable section
namespace CubicFirstMoment

def angularLiftResidueChar {q : Eisenstein} (η : MulChar (Residues q) ℂ) (ℓ : ℤ) :
    MulChar (Residues (q*3)) ℂ :=
  productResidueChar η (angularCorrectionChar ℓ)

lemma angularLiftResidueChar_primary {q n : Eisenstein}
    (η : MulChar (Residues q) ℂ) (ℓ : ℤ) (hn : primary n) :
    angularLiftResidueChar η ℓ (Ideal.Quotient.mk (modulus (q*3)) n) =
      η (Ideal.Quotient.mk (modulus q) n) := by
  rw [angularLiftResidueChar,productResidueChar_mk,angularCorrectionChar_mk,
    angularUnitCorrection_primary hn,mul_one]

lemma angularLiftResidueChar_compatible {q : Eisenstein}
    (η : MulChar (Residues q) ℂ) (ℓ : ℤ)
    (hu : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) u) = 1) :
    AngularUnitCompatible (q*3) (angularLiftResidueChar η ℓ) ℓ := by
  exact productResidueChar_angular_units η (angularCorrectionChar ℓ) hu
    (angularCorrectionChar_unit ℓ)

lemma productResidueChar_angular_units_right {q r : Eisenstein}
    (χ : MulChar (Residues q) ℂ) (η : MulChar (Residues r) ℂ)
    {ℓ : ℤ} (hχ : AngularUnitCompatible q χ ℓ)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1) :
    AngularUnitCompatible (q*r) (productResidueChar χ η) ℓ := by
  intro u
  rw [productResidueChar_mk,hη u,mul_one]
  exact hχ u

def structuredAngularTwistModulus (v e : Eisenstein) : Eisenstein :=
  structuredTwistModulus v e*3

def structuredAngularTwistCharacter (hperiod : CubicSupplementaryPeriodicity)
    (v e : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) :
    MulChar (Residues (structuredAngularTwistModulus v e)) ℂ :=
  angularLiftResidueChar (structuredTwistCharacter hperiod v e hv) ℓ

lemma structuredAngularTwistModulus_ne_zero {v e : Eisenstein}
    (hv : v ≠ 0) (he : e ≠ 0) : structuredAngularTwistModulus v e ≠ 0 :=
  mul_ne_zero (structuredTwistModulus_ne_zero hv he) (by norm_num)

lemma structuredAngularTwistCharacter_compatible
    (hperiod : CubicSupplementaryPeriodicity) (v e : Eisenstein) (hv : v ≠ 0) (ℓ : ℤ) :
    AngularUnitCompatible (structuredAngularTwistModulus v e)
      (structuredAngularTwistCharacter hperiod v e hv ℓ) ℓ :=
  angularLiftResidueChar_compatible _ ℓ (structuredTwistCharacter_units hperiod v e hv)

lemma structuredAngularTwistModulus_bound {Y δ d : ℝ} (hY : 1 ≤ Y) (hd : 3*δ ≤ d)
    (h729 : 729 ≤ Y^δ) {v e : Eisenstein} (hv : norm v ≤ Y^δ) (he : norm e ≤ Y^δ) :
    norm (structuredAngularTwistModulus v e) ≤ Y^d := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have h9 : norm (9:Eisenstein) = 81 := by
    change Complex.normSq (9:ℂ) = 81
    norm_num
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num
  calc
    norm (structuredAngularTwistModulus v e) = 729*(norm v*norm e) := by
      simp only [structuredAngularTwistModulus,structuredTwistModulus,one_mul,norm_mul_eq,h9,h3]
      ring
    _ ≤ 729*(Y^δ*Y^δ) := by gcongr; exact norm_nonneg e
    _ ≤ Y^δ*(Y^δ*Y^δ) := by gcongr
    _ = Y^(3*δ) := by rw [← Real.rpow_add hYp,← Real.rpow_add hYp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hd

end CubicFirstMoment

end

end OAI
