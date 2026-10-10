import OAI.NumberTheory.CubicMoment.Estimates.TwistedIdealMatch
import OAI.NumberTheory.CubicMoment.Angular.AngularPrimitiveDualMoments
import OAI.NumberTheory.CubicMoment.Estimates.SupportedIdealParts

namespace OAI

/-! Agreement with the actual small-twisted mixed coefficients outside
three and the small modulus, including every common zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angular_twisted_ideal_mixed_match {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) (hν : primary (idealPrimaryGenerator ν))
    (hνr : IsCoprime r (idealPrimaryGenerator ν)) :
    angularResidueIdealChar d ψ ℓ ν = primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν := by
  rw [angularResidueIdealChar_primaryNormalize ψ hu ν,
    angularResidueIdealChar_primaryNormalize η hη ν,
    twisted_character_primary_match ha hb ψ η
      (twisted_conductor_contains ha hb hsa hsb hab hsmall ψ η hagree) hagree hν hνr,
    primaryMixedIdealChar_eq,ite_eq_left hν]
  ring

 theorem angularTwistedDualPolynomial_supported_partition {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (S : Finset EisensteinIdealExponent) (J u : ℝ) :
    normalizedDualPolynomial S (angularResidueIdealChar d ψ ℓ) idealExponentNorm J u =
      ∑ ρ ∈ supportedParts (3*r) S,
        (angularResidueIdealChar d ψ ℓ ρ*mellinPhase u (idealExponentNorm ρ))*
          normalizedDualPolynomial (outsideFiber (3*r) S ρ)
            (fun ν => primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν)
            idealExponentNorm (J/idealExponentNorm ρ) u := by
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have h3 : (3:Eisenstein) ∣ 3*r := dvd_mul_right 3 r
  rw [normalizedDualPolynomial_supported_partition (3*r) S _ (angularResidueIdealChar_add d ψ ℓ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  unfold normalizedDualPolynomial
  apply Finset.sum_congr rfl
  intro ν hν
  rw [angular_twisted_ideal_mixed_match ha hb hsa hsb hab hsmall ψ η ℓ hu hη hagree ν
    (outsideFiber_primary h3r h3 hν)
    (outsideFiber_coprime h3r h3 hν).symm.of_mul_left_right]

end CubicFirstMoment

end

end OAI
