import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialIntegerGrid
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! # Smoothness of the polynomial extensions of lattice maps -/

noncomputable section
namespace PolycyclicRecognition

theorem IsCoordinatePolynomial.contDiff {I J : Type*} [Fintype I] [Fintype J]
    {f : (I → ℝ) → (J → ℝ)} (hf : IsCoordinatePolynomial f) : ContDiff ℝ ⊤ f := by
  obtain ⟨p, hp⟩ := hf
  apply contDiff_pi.mpr
  intro j
  have he : (fun x => f x j) = (fun x => MvPolynomial.eval x (p j)) := by
    funext x
    exact (hp x j).symm
  rw [he]
  exact (AnalyticOnNhd.eval_mvPolynomial (p j)).contDiff

end PolycyclicRecognition

end

end OAI
