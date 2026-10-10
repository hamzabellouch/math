import OAI.NumberTheory.CubicMoment.Estimates.PrimeIdealEulerExclusion
import OAI.NumberTheory.CubicMoment.Estimates.PrimeIdealPrimaryTransfer
import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeCharacter

namespace OAI

/-! Prime-ideal Euler-factor restoration and exact primary-prime transfer
for fixed angular characters, retaining the original modulus at three. -/
noncomputable section
namespace CubicFirstMoment

theorem induced_angular_prime_error {q d : Eisenstein} (hq : q ≠ 0) (hd : d ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ℓ : ℤ) (X : ℝ) :
    ‖idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X-
      idealPrimeChebyshev (angularResidueIdealChar d ψ ℓ) X‖ ≤ Real.log (norm q) := by
  have he : angularResidueIdealChar q χ ℓ =
      primeIdealRestriction (idealExponentOf q).support (angularResidueIdealChar d ψ ℓ) :=
    funext (induced_angularResidueIdealChar hq h ℓ)
  rw [he,norm_sub_rev]
  have hh := primeIdeal_restriction_norm_cost (idealExponentOf q)
    (angularResidueIdealChar d ψ ℓ) (angularResidueIdealChar_norm_le_one hd ψ ℓ) X
  rwa [idealExponentOf_norm hq] at hh

lemma residueIdealChar_zero_nonprimary {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent)
    (hn : ¬primary (idealPrimaryGenerator ν)) : residueIdealChar q χ ν=0 := by
  have hnc : ¬IsCoprime q (idealExponentGenerator ν) := by
    intro hc
    have hcop := (hc.of_isCoprime_of_dvd_left h3).symm
    apply hn
    exact (idealPrimaryGenerator_primary_iff ν).mpr ((idealGenerator_coprime_three_iff ν).mp hcop)
  exact MulChar.map_nonunit χ (fun hu => hnc (isCoprime_of_residue_isUnit hu))

lemma angularResidueIdealChar_zero_nonprimary {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent)
    (hn : ¬primary (idealPrimaryGenerator ν)) : angularResidueIdealChar q χ ℓ ν=0 := by
  rw [angularResidueIdealChar,residueIdealChar_zero_nonprimary h3 χ ν hn,zero_mul]

theorem angular_primeChebyshev_eq_ideal {q : Eisenstein} (h3 : (3:Eisenstein) ∣ q)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ) (X : ℝ) :
    primeChebyshev (fun p => χ (Ideal.Quotient.mk (modulus q) p)*theta ℓ p) X =
      idealPrimeChebyshev (angularResidueIdealChar q χ ℓ) X := by
  symm
  apply idealPrimeChebyshev_primary_sum
  · exact angularResidueIdealChar_zero_nonprimary h3 χ ℓ
  · intro a ha
    exact angularResidueIdealChar_at_element χ hu (primary_ne_zero ha)

end CubicFirstMoment

end

end OAI
