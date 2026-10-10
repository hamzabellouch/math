import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateCurves
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialMatrixLieRepresentation

namespace OAI

/-! # Polynomial entries along one-parameter subgroups -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n m : ℕ}
  (b : Module.Basis (Fin n) ℝ L)

theorem polynomial_translated_coordinateFunction {f : L → ℝ}
    (hf : f ∈ coordinateOrbitSpan (polynomialModelCoordinate b)) (a v : L) :
    (fun t : ℝ => f (a * (t • v))) ∈ polynomialFunctions := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hf
    exact hasPolynomialLineCoordinates_mul b _ _
      (hasPolynomialLineCoordinates_mul b _ _ (hasPolynomialLineCoordinates_const b a)
        (hasPolynomialLineCoordinates_line b v)) (hasPolynomialLineCoordinates_const b h) i
  | zero => exact polynomialFunctions.zero_mem
  | add f g _ _ hf hg => exact polynomialFunctions.add_mem hf hg
  | smul c f _ hf => exact polynomialFunctions.smul_mem c hf

variable (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

theorem polynomial_coordinateActionInBasis (v : L) (u : Fin m → ℝ) (i : Fin m) :
    (fun t : ℝ => coordinateActionInBasis b B (t • v) u i) ∈ polynomialFunctions := by
  let e : (Fin m → ℝ) →ₗ[ℝ] (L → ℝ) :=
    (coordinateOrbitSpan (polynomialModelCoordinate b)).subtype.comp B.toLinearMap
  have he : Function.Injective e := Subtype.coe_injective.comp B.injective
  apply polynomial_of_coordinateEvaluations e he
    (fun t => coordinateActionInBasis b B (t • v) u) ?_ (LinearMap.proj i)
  intro a
  have heq : (fun t : ℝ => e (coordinateActionInBasis b B (t • v) u) a) =
      (fun t => (B u : L → ℝ) (a * (t • v))) := by
    funext t
    exact coordinateActionInBasis_eval b B (t • v) u a
  rw [heq]
  exact polynomial_translated_coordinateFunction b (B u).2 a v

theorem polynomial_matrixRepresentation_entry (v : L) (i j : Fin m) :
    ∃ p : Polynomial ℝ, ∀ t : ℝ, p.eval t =
      (polynomialMatrixRepresentation b B (t • v) : Matrix (Fin m) (Fin m) ℝ) i j :=
  mem_polynomialFunctions_iff.mp (polynomial_coordinateActionInBasis b B v (Pi.single j 1) i)

end PolycyclicRecognition

end

end OAI
