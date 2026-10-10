import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorPolynomialBox

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial ElementaryPositivity.CenterCalculus
open scoped TensorProduct

lemma box_assoc {A B C α β γ : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C]
    (p : MvPolynomial α A) (q : MvPolynomial β B) (r : MvPolynomial γ C) :
    extendPolynomial (Algebra.TensorProduct.assoc ℚ ℚ ℚ A B C).toAlgHom (Equiv.sumAssoc α β γ)
      (box (box p q) r)=box p (box q r) := by
  change extendPolynomial _ _
    (extendPolynomial (Algebra.TensorProduct.includeLeft : A⊗[ℚ]B →ₐ[ℚ] (A⊗[ℚ]B)⊗[ℚ]C) Sum.inl
      (extendPolynomial (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A⊗[ℚ]B) Sum.inl p *
       extendPolynomial (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A⊗[ℚ]B) Sum.inr q) *
     extendPolynomial (Algebra.TensorProduct.includeRight : C →ₐ[ℚ] (A⊗[ℚ]B)⊗[ℚ]C) Sum.inr r)=
    extendPolynomial (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A⊗[ℚ](B⊗[ℚ]C)) Sum.inl p *
    extendPolynomial (Algebra.TensorProduct.includeRight : B⊗[ℚ]C →ₐ[ℚ] A⊗[ℚ](B⊗[ℚ]C)) Sum.inr
      (extendPolynomial (Algebra.TensorProduct.includeLeft : B →ₐ[ℚ] B⊗[ℚ]C) Sum.inl q *
       extendPolynomial (Algebra.TensorProduct.includeRight : C →ₐ[ℚ] B⊗[ℚ]C) Sum.inr r)
  simp only [map_mul,extendPolynomial_comp]
  rw [mul_assoc]
  congr 2

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
