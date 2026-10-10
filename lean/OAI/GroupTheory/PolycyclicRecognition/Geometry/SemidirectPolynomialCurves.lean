import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectCoordinateOrbit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCurveOperations

namespace OAI

/-! # Polynomial scalar curves in semidirect coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

def HasSemidirectPolynomialCoordinates (F : ℝ → L × ℝ) : Prop :=
  ∀ i, (fun t => semidirectCoordinate b i (F t)) ∈ polynomialFunctions

omit [FiniteDimensional ℝ L] P in
theorem hasSemidirectPolynomialCoordinates_const (v : L × ℝ) :
    HasSemidirectPolynomialCoordinates b (fun _ => v) :=
  fun _ => polynomialFunctions_const _

omit [FiniteDimensional ℝ L] P in
theorem hasSemidirectPolynomialCoordinates_line (v : L × ℝ) :
    HasSemidirectPolynomialCoordinates b (fun t => t • v) := by
  intro i
  cases i with
  | inl i => exact hasPolynomialLineCoordinates_line b v.1 i
  | inr i => exact polynomialFunctions_linear v.2

theorem hasSemidirectPolynomialCoordinates_mul (F H : ℝ → L × ℝ)
    (hF : HasSemidirectPolynomialCoordinates b F)
    (hH : HasSemidirectPolynomialCoordinates b H) :
    HasSemidirectPolynomialCoordinates b
      (fun t => (derivationSemidirectGroup D hD).mul (F t) (H t)) := by
  intro i
  cases i with
  | inl j =>
    have hf : HasPolynomialLineCoordinates b (fun t => (F t).1) := fun i => hF (.inl i)
    have hh : HasPolynomialLineCoordinates b (fun t => (H t).1) := fun i => hH (.inl i)
    have hflow := hasPolynomialLineCoordinates_derivationFlow b D hD
      (fun t => (F t).2) (fun t => (H t).1) (hF (.inr ())) hh
    have hp := hasPolynomialLineCoordinates_dynkin b P.coefficients
      ![(fun t => (F t).1), (fun t => nilpotentDerivationFlow D hD (F t).2 (H t).1)]
      (by intro i; fin_cases i; exact hf; exact hflow) j
    change (fun t => b.repr ((F t).1 * nilpotentDerivationFlow D hD (F t).2 (H t).1) j) ∈ _
    have heq (t : ℝ) :
        (fun i : Fin 2 => ![(fun t => (F t).1),
          (fun t => nilpotentDerivationFlow D hD (F t).2 (H t).1)] i t) =
        ![(F t).1, nilpotentDerivationFlow D hD (F t).2 (H t).1] := by
      funext i
      fin_cases i <;> rfl
    simpa only [P.mul_eq, heq] using hp
  | inr j => exact polynomialFunctions.add_mem (hF (.inr ())) (hH (.inr ()))

theorem semidirect_translated_line_polynomial (a v z : L × ℝ) :
    ∀ i, (fun t : ℝ => semidirectCoordinate b i
      ((derivationSemidirectGroup D hD).mul ((derivationSemidirectGroup D hD).mul a (t • v)) z)) ∈ polynomialFunctions := by
  exact hasSemidirectPolynomialCoordinates_mul b D hD _ _
    (hasSemidirectPolynomialCoordinates_mul b D hD _ _
      (hasSemidirectPolynomialCoordinates_const b a)
      (hasSemidirectPolynomialCoordinates_line b v))
    (hasSemidirectPolynomialCoordinates_const b z)

end PolycyclicRecognition

end

end OAI
