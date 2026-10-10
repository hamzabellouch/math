import OAI.NumberTheory.CubicMoment.Estimates.TwistedConductor

namespace OAI

/-! Actual primitive reduction after a fixed small character twist. The
variable squarefree conductor is detected, rather than postulated. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem twisted_mixed_primitive_conductor {a b r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (hnu : ¬ IsUnit (a*b)) (η : MulChar (Residues r) ℂ)
    (hη : ∀ u : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) u) = 1) :
    ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
      normNat d ≤ normNat ((3*(a*b))*r) ∧ a*b ∣ d ∧
      (∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1) ∧
      ResidueCharacterInduces ((3*(a*b))*r) d
        (productResidueChar (primaryMixedResidueChar a b ha hb) η) ψ ∧
      (∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ (Ideal.Quotient.mk (modulus d) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) := by
  have hq : (3*(a*b))*r ≠ (0:Eisenstein) :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (mul_ne_zero (primary_ne_zero ha) (primary_ne_zero hb))) hr
  obtain ⟨d,ψ,hd,hind,hN,hprim⟩ := primitive_residue_conductor_exists hq
    (productResidueChar (primaryMixedResidueChar a b ha hb) η)
  have hqx (x : Eisenstein) (hx : primary x) (hcop : IsCoprime (a*b*r) x) :
      IsCoprime ((3*(a*b))*r) x :=
    ((primary_coprime_three hx).symm.mul_left hcop.of_mul_left_left).mul_left
      hcop.of_mul_left_right
  have hagree (x : Eisenstein) (hx : primary x) (hcop : IsCoprime (a*b*r) x) :
      ψ (Ideal.Quotient.mk (modulus d) x) =
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x) := by
    rw [hind.2 x (hqx x hx hcop),productResidueChar_mk,
      primaryMixedResidueChar_primary ha hb hx]
  have hdiv := twisted_conductor_contains ha hb hsa hsb hab hsmall ψ η hagree
  have hn : ψ ≠ 1 := by
    intro he
    have h1 (x : Eisenstein) (hx : primary x) (hcop : IsCoprime (a*b*r) x) :
        (1 : MulChar (Residues (1:Eisenstein)) ℂ) (Ideal.Quotient.mk (modulus 1) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x) := by
      have hg := hagree x hx hcop
      rw [he,MulChar.one_apply (residue_isUnit_of_isCoprime
        ((hqx x hx hcop).of_isCoprime_of_dvd_left hind.1))] at hg
      rw [MulChar.one_apply (residue_isUnit_of_isCoprime (isCoprime_one_left))]
      exact hg
    exact hnu (isUnit_of_dvd_one
      (twisted_conductor_contains ha hb hsa hsb hab hsmall 1 η h1))
  refine ⟨d,ψ,hd,hprim,hn,hN,hdiv,?_,hind,hagree⟩
  exact hind.global_units (productResidueChar_units _ η
    (primaryMixedResidueChar_trivialInfinity ha hb) hη)

end CubicFirstMoment

end

end OAI
