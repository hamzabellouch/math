import OAI.NumberTheory.CubicMoment.Estimates.TwistedPrimitive
import OAI.NumberTheory.CubicMoment.Estimates.MixedPrimitiveData

namespace OAI

/-! Choosing the actual primitive characters for a finite family, with
uniform arithmetic conductor bounds. -/
noncomputable section
namespace CubicFirstMoment

def PrimitiveSmallTwistSpecification (a b r d : Eisenstein)
    (η : MulChar (Residues r) ℂ) (ψ : MulChar (Residues d) ℂ) : Prop :=
  d ≠ 0 ∧ PrimitiveResidueCharacter d ψ ∧ ψ ≠ 1 ∧
  (∀ v : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) v) = 1) ∧
  (∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
    ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) ∧
  (residueHeckeScale d)^2 ≤ 27*norm a*norm b*norm r/(2*Real.pi)^2

 theorem actual_primitive_smalltwist_family (P : Finset Eisenstein) {b r : Eisenstein}
    (hb : primary b) (hsb : Squarefree b) (hr : r ≠ 0) (η : MulChar (Residues r) ℂ)
    (hη : ∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus r) v) = 1)
    (hP : ∀ a ∈ P, primary a ∧ Squarefree a ∧ IsCoprime a b ∧ ¬ IsUnit (a*b))
    (hsmall : ∀ a ∈ P, IsCoprime (a*b) r) :
    ∃ (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ),
      ∀ a ∈ P, PrimitiveSmallTwistSpecification a b r (d a) η (ψ a) := by
  have hex (a : Eisenstein) : ∃ (d : Eisenstein) (ψ : MulChar (Residues d) ℂ),
      a ∈ P → PrimitiveSmallTwistSpecification a b r d η ψ := by
    by_cases ha : a ∈ P
    · obtain ⟨d,ψ,hd,hprim,hn,hN,_,hu,_,hag⟩ := twisted_mixed_primitive_conductor
        (hP a ha).1 hb (hP a ha).2.1 hsb (hP a ha).2.2.1 hr
        (hsmall a ha) (hP a ha).2.2.2 η hη
      refine ⟨d,ψ,fun _ => ⟨hd,hprim,hn,hu,hag,?_⟩⟩
      have h3 : norm (3:Eisenstein) = 9 := by
        change Complex.normSq (3:ℂ) = 9
        norm_num [Complex.normSq]
      have hN' : norm d ≤ 9*norm a*norm b*norm r := by
        have h : norm d ≤ norm ((3*(a*b))*r) := by
          simpa only [normNat_cast] using (Nat.cast_le (α := ℝ).mpr hN)
        calc
          norm d ≤ norm ((3*(a*b))*r) := h
          _ = _ := by rw [norm_mul_eq,norm_mul_eq,norm_mul_eq,h3]; ring
      rw [residueHeckeScale_sq hd]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    · exact ⟨1,1,fun h => False.elim (ha h)⟩
  choose d ψ hspec using hex
  exact ⟨d,ψ,hspec⟩

end CubicFirstMoment

end

end OAI
