import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateOperations
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGroupLaws

namespace OAI

/-! # Polynomial coordinate formulas for the finite BCH words -/

noncomputable section
namespace PolycyclicRecognition
variable {I J : Type*} {d : ℕ}

theorem coordinatePolynomial_evalBilinearWord
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (X : (I → ℝ) → J → (Fin d → ℝ))
    (hX : ∀ j, IsCoordinatePolynomial (fun x => X x j)) (w : FreeMagma J) :
    IsCoordinatePolynomial (fun x => evalBilinearWord B (X x) w) := by
  induction w using FreeMagma.rec with
  | of j => exact hX j
  | mul a b ha hb =>
    exact IsCoordinatePolynomial.bilinear B.toLinearMap₁₂ ha hb

theorem coordinatePolynomial_bilinearDynkin {c n : ℕ} (a : DynkinCoefficients c n)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (X : (I → ℝ) → Fin n → (Fin d → ℝ))
    (hX : ∀ j, IsCoordinatePolynomial (fun x => X x j)) :
    IsCoordinatePolynomial (fun x => bilinearDynkinPolynomial a B (X x)) := by
  apply IsCoordinatePolynomial.sum Finset.univ
  intro k _
  apply IsCoordinatePolynomial.sum Finset.univ
  intro w _
  exact (coordinatePolynomial_evalBilinearWord B X hX (rightNestedWord k.val w)).smul _

theorem coordinatePolynomial_dynkinProduct {c : ℕ} (a : DynkinCoefficients c 2)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    IsCoordinatePolynomial (fun x : (Fin d ⊕ Fin d) → ℝ =>
      dynkinProduct a B (x ∘ Sum.inl) (x ∘ Sum.inr)) := by
  apply coordinatePolynomial_bilinearDynkin
  intro i
  fin_cases i
  · exact IsCoordinatePolynomial.reindex Sum.inl
  · exact IsCoordinatePolynomial.reindex Sum.inr

end PolycyclicRecognition

end

end OAI
