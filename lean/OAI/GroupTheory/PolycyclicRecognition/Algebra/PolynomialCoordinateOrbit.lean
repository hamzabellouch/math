import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateOrbitRepresentation
import Mathlib.Algebra.MvPolynomial.Eval

namespace OAI

/-! # Finite-dimensional coordinate orbits from polynomial multiplication

The coefficients may be arbitrary functions of the right factor. Only the
finite polynomial dependence on the left coordinates is needed here.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G I : Type*} [Group G] (q : I → G → ℝ)

def coordinateMonomial (d : I →₀ ℕ) : G → ℝ :=
  fun x => ∏ i ∈ d.support, q i x ^ d i

def coordinatePolynomialEvaluation (p : MvPolynomial I (G → ℝ)) (g : G) : G → ℝ :=
  fun x => p.eval₂ (Pi.evalRingHom (fun _ : G => ℝ) g) (fun i => q i x)

omit [Group G] in
theorem coordinatePolynomialEvaluation_eq_sum (p : MvPolynomial I (G → ℝ)) (g : G) :
    coordinatePolynomialEvaluation q p g =
      ∑ d ∈ p.support, (p.coeff d g) • coordinateMonomial q d := by
  classical
  funext x
  rw [coordinatePolynomialEvaluation, MvPolynomial.eval₂_eq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coordinateMonomial]
  rfl

theorem finiteDimensional_coordinateOrbitSpan_of_polynomial [Finite I]
    (p : I → MvPolynomial I (G → ℝ))
    (hmul : ∀ (g : G) (i : I) (x : G),
      q i (x * g) = coordinatePolynomialEvaluation q (p i) g x) :
    FiniteDimensional ℝ (coordinateOrbitSpan q) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let J := Σ i : I, ↥(p i).support
  let : Fintype J := by dsimp [J]; infer_instance
  let b : J → G → ℝ := fun j => coordinateMonomial q j.2.val
  apply finiteDimensional_coordinateOrbitSpan q b
  intro g i
  have heq : (fun x => q i (x * g)) = coordinatePolynomialEvaluation q (p i) g :=
    funext (hmul g i)
  rw [heq, coordinatePolynomialEvaluation_eq_sum]
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨i, ⟨d, hd⟩⟩, rfl⟩

end PolycyclicRecognition

end

end OAI
