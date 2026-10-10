import OAI.Geometry.SurfaceImmersion.Atlas.RelativePhaseCancellation

namespace OAI

/-! Polynomial closure for the complete fixed-cover cancellation constants. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseGeometry
open RealModes JetPolynomial JetPolynomial.Perturbation

lemma fixed_cancellation_budgets_polynomial (N q m : ℕ)
    (J S A : ℕ → ℝ) (p : ℕ → ℕ) (B : ℕ → ℝ → ℝ) {D : ℝ}
    (hJ : ∀ r, 1 ≤ J r) (hS : ∀ r, 1 ≤ S r) (hA : ∀ r, 1 ≤ A r) (hD : 1 ≤ D)
    (hB : ∀ r, HasPolynomialBound (B r)) (hB1 : ∀ r x, 1 ≤ x → 1 ≤ B r x) :
    HasPolynomialBound (fun x => (N : ℝ)*splitSizeBudget q m
      (fun r => A r*(fixedChartSolverBudget J (fun j => B j x) D r)^(p r))
      (fixedChartSolverBudget J (fun j => B j x) D) J S) ∧
    HasPolynomialBound (fun x => (N : ℝ)*splitResidualBudget q m
      (fun r => A r*(fixedChartSolverBudget J (fun j => B j x) D r)^(p r))
      (fixedChartSolverBudget J (fun j => B j x) D) J S) := by
  let E : ℕ → ℝ → ℝ := fun r x => fixedChartSolverBudget J (fun j => B j x) D r
  have hE (r : ℕ) : HasPolynomialBound (E r) :=
    fixedChartSolverBudget_polynomial J B (fun r => zero_le_one.trans (hJ r))
      (zero_le_one.trans hD) hB r
  have hE1 (r : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ E r x := by
    have hb0 := zero_le_one.trans (hB1 r x hx)
    have hj0 := zero_le_one.trans (hJ (r+3))
    have hd0 := zero_le_one.trans hD
    have hs0 := sq_nonneg (J 1)
    dsimp [E,fixedChartSolverBudget]
    linarith
  have hC (r : ℕ) : HasPolynomialBound (fun x => A r*(E r x)^(p r)) :=
    (polynomialBound_const (zero_le_one.trans (hA r))).mul ((hE r).pow (p r))
  have hC1 (r : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ A r*(E r x)^(p r) :=
    one_le_mul_of_one_le_of_one_le (hA r) (one_le_pow₀ (hE1 r x hx))
  have hJp (r : ℕ) : HasPolynomialBound (fun _ : ℝ => J r) :=
    polynomialBound_const (zero_le_one.trans (hJ r))
  have hSp (r : ℕ) : HasPolynomialBound (fun _ : ℝ => S r) :=
    polynomialBound_const (zero_le_one.trans (hS r))
  exact ⟨(polynomialBound_const (Nat.cast_nonneg N)).mul
    (splitSizeBudget_polynomial q m (fun r x => A r*(E r x)^(p r)) E
      (fun r _ => J r) (fun r _ => S r) hC hE hJp hSp hC1),
    (polynomialBound_const (Nat.cast_nonneg N)).mul
    (splitResidualBudget_polynomial q m (fun r x => A r*(E r x)^(p r)) E
      (fun r _ => J r) (fun r _ => S r) hC hE hJp hSp hC1)⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
