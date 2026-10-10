import OAI.Geometry.SurfaceImmersion.Geometry.MetricForcedFactorBudgets
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticTargetBudget

namespace OAI

/-! The full quadratic solve budgets, with finite derivative loss explicit. -/
noncomputable section
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes

def quadraticInputBudget (m : ℕ) (D I α β : ℕ → ℝ) : ℝ :=
  tensorChartBudget m (I m) (I (m+1))*quadraticTargetBudget m (D m) (α m) (β m)

def quadraticSizeBudget (q m : ℕ) (D C J I α β : ℕ → ℝ) : ℝ :=
  max 1 (metricForcedSizeBudget C J (fun _ => 1) q m) * quadraticInputBudget (m+q+1) D I α β

def quadraticResidualBudget (q m : ℕ) (D C J I α β : ℕ → ℝ) : ℝ :=
  max 1 (metricForcedResidualBudget C J (fun _ => 1) q m) * quadraticInputBudget (m+q+1) D I α β

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

lemma quadraticInputBudget_polynomial (m : ℕ) (D I α β : ℕ → ℝ → ℝ)
    (hD : ∀ k, HasPolynomialBound (D k)) (hI : ∀ k, HasPolynomialBound (I k))
    (hα : ∀ k, HasPolynomialBound (α k)) (hβ : ∀ k, HasPolynomialBound (β k)) :
    HasPolynomialBound (fun x => quadraticInputBudget m
      (fun k => D k x) (fun k => I k x) (fun k => α k x) (fun k => β k x)) :=
  (tensorChartBudget_polynomial m (I m) (I (m+1)) (hI m) (hI (m+1))).mul
    (quadraticTargetBudget_polynomial m (D m) (α m) (β m) (hD m) (hα m) (hβ m))

lemma quadraticSizeBudget_polynomial (q m : ℕ) (D C J I α β : ℕ → ℝ → ℝ)
    (hD : ∀ k, HasPolynomialBound (D k)) (hC : ∀ k, HasPolynomialBound (C k))
    (hJ : ∀ k, HasPolynomialBound (J k)) (hI : ∀ k, HasPolynomialBound (I k))
    (hα : ∀ k, HasPolynomialBound (α k)) (hβ : ∀ k, HasPolynomialBound (β k))
    (hC1 : ∀ k x, 1 ≤ x → 1 ≤ C k x) :
    HasPolynomialBound (fun x => quadraticSizeBudget q m
      (fun k => D k x) (fun k => C k x) (fun k => J k x)
      (fun k => I k x) (fun k => α k x) (fun k => β k x)) :=
  ((polynomialBound_const zero_le_one).max (metricForcedSizeBudget_polynomial C J (fun _ _ => 1) hC hJ
    (fun _ => polynomialBound_const zero_le_one) hC1 q m)).mul
    (quadraticInputBudget_polynomial (m+q+1) D I α β hD hI hα hβ)

lemma quadraticResidualBudget_polynomial (q m : ℕ) (D C J I α β : ℕ → ℝ → ℝ)
    (hD : ∀ k, HasPolynomialBound (D k)) (hC : ∀ k, HasPolynomialBound (C k))
    (hJ : ∀ k, HasPolynomialBound (J k)) (hI : ∀ k, HasPolynomialBound (I k))
    (hα : ∀ k, HasPolynomialBound (α k)) (hβ : ∀ k, HasPolynomialBound (β k))
    (hC1 : ∀ k x, 1 ≤ x → 1 ≤ C k x) :
    HasPolynomialBound (fun x => quadraticResidualBudget q m
      (fun k => D k x) (fun k => C k x) (fun k => J k x)
      (fun k => I k x) (fun k => α k x) (fun k => β k x)) :=
  ((polynomialBound_const zero_le_one).max (metricForcedResidualBudget_polynomial C J (fun _ _ => 1) hC hJ
    (fun _ => polynomialBound_const zero_le_one) hC1 q m)).mul
    (quadraticInputBudget_polynomial (m+q+1) D I α β hD hI hα hβ)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
