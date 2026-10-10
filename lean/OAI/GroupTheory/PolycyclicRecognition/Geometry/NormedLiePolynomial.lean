import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieWordDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! # Smooth Lie polynomials in a compatible finite-dimensional norm -/

noncomputable section
namespace PolycyclicRecognition

open scoped ContDiff

variable {L V I : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {r : ℕ∞ω}

theorem contDiff_normed_evalBracketWord (X : V → I → L)
    (hX : ∀ i, ContDiff ℝ r (fun v => X v i)) (w : FreeMagma I) :
    ContDiff ℝ r (fun v => evalBracketWord (X v) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul u v hu hv =>
    exact ((normedLieBracket (L := L)).contDiff.comp hu).clm_apply hv

theorem contDiff_normed_finiteDynkinPolynomial {c n : ℕ}
    (coeff : DynkinCoefficients c n) (X : V → Fin n → L)
    (hX : ∀ i, ContDiff ℝ r (fun v => X v i)) :
    ContDiff ℝ r (fun v => finiteDynkinPolynomial coeff (X v)) := by
  apply ContDiff.sum
  intro d _
  apply ContDiff.sum
  intro w _
  exact (contDiff_normed_evalBracketWord X hX (rightNestedWord d.val w)).const_smul _

end PolycyclicRecognition

end

end OAI
