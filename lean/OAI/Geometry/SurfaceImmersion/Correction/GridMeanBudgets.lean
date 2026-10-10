import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLinearMeanBudgets
import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseCutoffBounds

namespace OAI

/-! Polynomial growth of the actual grid mean budgets in the inverse grid scale. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open RealModes JetPolynomial

def gridMeanBudget (p : ℕ → ℕ) (A L : ℕ → ℝ) (B : ℕ → ℝ → ℝ)
    (m : ℕ) (x : ℝ) : ℝ :=
  linearMeanGeometryBudget p A (fun j => B j x)
    (fun j => 1+phaseCutoffBudget j (L j*x^(6*j)) (B j x) 1) m

lemma gridMeanBudget_polynomial (p : ℕ → ℕ) (A L : ℕ → ℝ)
    (B : ℕ → ℝ → ℝ) (hA : ∀ m, 0 ≤ A m) (hL : ∀ m, 0 ≤ L m)
    (hB : ∀ m, HasPolynomialBound (B m)) (m : ℕ) :
    HasPolynomialBound (gridMeanBudget p A L B m) := by
  apply linearMeanGeometryBudget_growth p A B _ hA hB
  intro j
  exact (polynomialBound_const zero_le_one).add
    (phaseCutoffBudget_polynomial j
      ((polynomialBound_const (hL j)).mul (polynomialBound_id.pow (6*j)))
      (hB j) (polynomialBound_const zero_le_one))

lemma gridMeanBudget_at_inverse (p : ℕ → ℕ) (A L : ℕ → ℝ)
    (B : ℕ → ℝ → ℝ) (m : ℕ) (z : ℝ) :
    gridMeanBudget p A L B m z⁻¹ =
      linearMeanGeometryBudget p A (fun j => B j z⁻¹)
        (fun j => 1+phaseCutoffBudget j (L j/z^(6*j)) (B j z⁻¹) 1) m := by
  simp only [gridMeanBudget,inv_pow,div_eq_mul_inv]

end ClosedSurfaceR4.PhaseMean

end

end OAI
