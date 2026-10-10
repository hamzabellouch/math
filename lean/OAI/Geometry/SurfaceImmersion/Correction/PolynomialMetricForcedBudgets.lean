import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSupportedModeBudgets
import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearChartedMeanData

namespace OAI

/-! Polynomial constants for the actual supported forced metric solver.
The scale factor in its residual is separated from its geometric budget. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes SmallModes

def metricForcedSizeBudget (C J N : ℕ → ℝ) (q m : ℕ) : ℝ :=
  (m.factorial : ℝ)*(2^m*(forcedModeBudget 4 0 C (fun _ => 0) q m*N (m+q+1)))*J m^m

def metricForcedResidualBudget (C J N : ℕ → ℝ) (q m : ℕ) : ℝ :=
  tensorChartBudget m (J m) (J (m+1)) * (2^m *
    FiniteParametrix.boundProfile 1 (fun r => errorConstant r (C r))
      (fun r => errorConstant r (C r)*N (r+1)) q m)

theorem metricForcedSizeBudget_polynomial (C J N : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (q m : ℕ) :
    HasPolynomialBound (fun x => metricForcedSizeBudget
      (fun r => C r x) (fun r => J r x) (fun r => N r x) q m) := by
  have hz : ∀ m : ℕ, HasPolynomialBound (fun _ : ℝ => (0 : ℝ)) :=
    fun _ => polynomialBound_const le_rfl
  exact ((polynomialBound_const (Nat.cast_nonneg m.factorial)).mul
    ((polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity)).mul
      ((forcedModeBudget_polynomial 4 0 C (fun _ _ => 0) hC hz hC1 q m).mul
        (hN (m+q+1))))).mul ((hJ m).pow m)

theorem metricForcedResidualBudget_polynomial (C J N : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (q m : ℕ) :
    HasPolynomialBound (fun x => metricForcedResidualBudget
      (fun r => C r x) (fun r => J r x) (fun r => N r x) q m) := by
  have he (r : ℕ) := (errorConstant_polynomial r).comp (hC r) (hC1 r)
  have hb := FiniteParametrix.boundProfile_polynomial 1
    (fun r x => errorConstant r (C r x))
    (fun r x => errorConstant r (C r x)*N (r+1) x) he
    (fun r => (he r).mul (hN (r+1))) q m
  have ht : HasPolynomialBound (fun x => tensorChartBudget m (J m x) (J (m+1) x)) := by
    unfold tensorChartBudget
    exact (polynomialBound_const (show (0 : ℝ) ≤ 4 by norm_num)).mul
      (((polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity)).mul
        (((polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity)).mul
          ((polynomialBound_const (Nat.cast_nonneg m.factorial)).mul ((hJ m).pow m))).mul
            (hJ (m+1)))).mul (hJ (m+1)))
  exact ht.mul ((polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity)).mul hb)

namespace PolynomialSolveData
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}

lemma metric_size_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0)
    (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ) :
    c.size f q m = metricForcedSizeBudget c.C c.J (c.norm f) q m := by
  have hD' : c.D = (fun _ => 0) := funext hD
  simp only [size,metricForcedSizeBudget,tensorOrder_emptyMetricPolynomial,hD',
    Nat.zero_add,mul_one]
  congr 2

lemma metric_residual_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0)
    (f : SupportedField (F := PhaseMean.ComplexTensor) (modeSupport K)) (q m : ℕ) :
    c.residual f q m = (τ/s)^(q+1)*metricForcedResidualBudget c.C c.J (c.norm f) q m := by
  have hκ : c.κ = fun r => errorConstant r (c.C r) := by
    funext r
    simp only [κ,hD r,zero_mul,max_eq_left (errorConstant_nonneg r (c.nonnegC r))]
  simp only [residual,metricForcedResidualBudget,hκ,tensorOrder_emptyMetricPolynomial,
    Nat.zero_add,zero_div,add_zero]
  ring

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
