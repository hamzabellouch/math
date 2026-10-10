import OAI.Geometry.SurfaceImmersion.Geometry.ExplicitSplitCancellation
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra

namespace OAI

/-! The explicit finite-chart constants have polynomial dependence on the
coordinate and splitting profiles. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation RealModes

lemma tensorChartBudget_polynomial (m : ℕ) (I J : ℝ → ℝ)
    (hI : HasPolynomialBound I) (hJ : HasPolynomialBound J) :
    HasPolynomialBound (fun x => tensorChartBudget m (I x) (J x)) := by
  unfold tensorChartBudget
  repeat first
    | exact hI
    | exact hJ
    | apply HasPolynomialBound.mul
    | apply HasPolynomialBound.pow
    | (apply polynomialBound_const; positivity)

lemma splitInputBudget_polynomial (q m : ℕ) (I S : ℕ → ℝ → ℝ)
    (hI : ∀ j, HasPolynomialBound (I j)) (hS : ∀ j, HasPolynomialBound (S j)) :
    HasPolynomialBound (fun x => splitInputBudget q m (fun j => I j x) (fun j => S j x)) := by
  unfold splitInputBudget
  exact (tensorChartBudget_polynomial _ _ _ (hI _) (hI _)).mul (hS _)

lemma splitSizeBudget_polynomial (q m : ℕ) (C J I S : ℕ → ℝ → ℝ)
    (hC : ∀ j, HasPolynomialBound (C j)) (hJ : ∀ j, HasPolynomialBound (J j))
    (hI : ∀ j, HasPolynomialBound (I j)) (hS : ∀ j, HasPolynomialBound (S j))
    (hC1 : ∀ j x, 1 ≤ x → 1 ≤ C j x) :
    HasPolynomialBound (fun x => splitSizeBudget q m
      (fun j => C j x) (fun j => J j x) (fun j => I j x) (fun j => S j x)) := by
  exact ((polynomialBound_const zero_le_one).max
    (metricForcedSizeBudget_polynomial C J (fun _ _ => 1) hC hJ
      (fun _ => polynomialBound_const zero_le_one) hC1 q m)).mul
        (splitInputBudget_polynomial q m I S hI hS)

lemma splitResidualBudget_polynomial (q m : ℕ) (C J I S : ℕ → ℝ → ℝ)
    (hC : ∀ j, HasPolynomialBound (C j)) (hJ : ∀ j, HasPolynomialBound (J j))
    (hI : ∀ j, HasPolynomialBound (I j)) (hS : ∀ j, HasPolynomialBound (S j))
    (hC1 : ∀ j x, 1 ≤ x → 1 ≤ C j x) :
    HasPolynomialBound (fun x => splitResidualBudget q m
      (fun j => C j x) (fun j => J j x) (fun j => I j x) (fun j => S j x)) := by
  exact ((polynomialBound_const zero_le_one).max
    (metricForcedResidualBudget_polynomial C J (fun _ _ => 1) hC hJ
      (fun _ => polynomialBound_const zero_le_one) hC1 q m)).mul
        (splitInputBudget_polynomial q m I S hI hS)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
