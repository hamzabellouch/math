import OAI.NumberTheory.CubicMoment.Estimates.TwistedPrimitive
import OAI.NumberTheory.CubicMoment.Estimates.SupportedIdealParts

namespace OAI

/-! Agreement with the actual small-twisted mixed coefficients outside
three and the small modulus, including every common zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma twisted_character_primary_match {a b d r x : Eisenstein}
    (ha : primary a) (hb : primary b) (ψ : MulChar (Residues d) ℂ)
    (η : MulChar (Residues r) ℂ) (hdiv : a*b ∣ d)
    (hagree : ∀ y : Eisenstein, primary y → IsCoprime (a*b*r) y →
      ψ (Ideal.Quotient.mk (modulus d) y) = mixedCubic a b y*η (Ideal.Quotient.mk (modulus r) y))
    (hx : primary x) (hxr : IsCoprime r x) :
    ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x) := by
  by_cases hcop : IsCoprime (a*b) x
  · exact hagree x hx (hcop.mul_left hxr)
  · have hz : mixedCubic a b x = 0 := mixedCubic_eq_zero_of_nonunit ha hb x
      (fun h => hcop (isCoprime_of_residue_isUnit h))
    rw [hz,zero_mul]
    apply MulChar.map_nonunit
    intro h
    exact hcop ((isCoprime_of_residue_isUnit h).of_isCoprime_of_dvd_left hdiv)

lemma twisted_ideal_mixed_match {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) (hν : primary (idealPrimaryGenerator ν))
    (hνr : IsCoprime r (idealPrimaryGenerator ν)) :
    residueIdealChar d ψ ν = primaryMixedIdealChar a b ν*residueIdealChar r η ν := by
  rw [residueIdealChar_primaryNormalize ψ hu ν,residueIdealChar_primaryNormalize η hη ν,
    twisted_character_primary_match ha hb ψ η
      (twisted_conductor_contains ha hb hsa hsb hab hsmall ψ η hagree) hagree hν hνr,
    primaryMixedIdealChar_eq,ite_eq_left hν]

 theorem twistedDualPolynomial_supported_partition {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (S : Finset EisensteinIdealExponent) (J u : ℝ) :
    normalizedDualPolynomial S (residueIdealChar d ψ) idealExponentNorm J u =
      ∑ ρ ∈ supportedParts (3*r) S,
        (residueIdealChar d ψ ρ*mellinPhase u (idealExponentNorm ρ))*
          normalizedDualPolynomial (outsideFiber (3*r) S ρ)
            (fun ν => primaryMixedIdealChar a b ν*residueIdealChar r η ν)
            idealExponentNorm (J/idealExponentNorm ρ) u := by
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have h3 : (3:Eisenstein) ∣ 3*r := dvd_mul_right 3 r
  rw [normalizedDualPolynomial_supported_partition (3*r) S _ (residueIdealChar_add d ψ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  unfold normalizedDualPolynomial
  apply Finset.sum_congr rfl
  intro ν hν
  rw [twisted_ideal_mixed_match ha hb hsa hsb hab hsmall ψ η hu hη hagree ν
    (outsideFiber_primary h3r h3 hν)
    (outsideFiber_coprime h3r h3 hν).symm.of_mul_left_right]

end CubicFirstMoment

end

end OAI
