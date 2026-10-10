import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMetricForcedBudgets
import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeResidual

namespace OAI

/-! Explicit polynomial budgets for the actual unperturbed free metric modes. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open RealModes SmallModes

def metricFreeSizeBudget (C J N : ℕ → ℝ) (q m : ℕ) : ℝ :=
  (m.factorial : ℝ)*2^m*correctedSeedBudget 0 C (fun _ => 0) q m (N (m+q+1))*J m^m

def metricFreeResidualBudget (C J N : ℕ → ℝ) (q m : ℕ) : ℝ :=
  tensorChartBudget m (J m) (J (m+1))*2^m*
    (FiniteParametrix.boundProfile 1 (fun r => errorConstant r (C r))
      (fun r => fullErrorConstant 4 r (C r)) q m * (Real.sqrt 2*2^(m+q+1)*N (m+q+1)))

theorem metricFreeSizeBudget_polynomial (C J N : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (q m : ℕ) :
    HasPolynomialBound (fun x => metricFreeSizeBudget
      (fun r => C r x) (fun r => J r x) (fun r => N r x) q m) := by
  have hz : ∀ m : ℕ, HasPolynomialBound (fun _ : ℝ => (0 : ℝ)) :=
    fun _ => polynomialBound_const le_rfl
  exact (((polynomialBound_const (Nat.cast_nonneg m.factorial)).mul
    (polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity))).mul
      (correctedSeedBudget_polynomial 0 C (fun _ _ => 0) (N (m+q+1)) hC hz
        (hN (m+q+1)) hC1 q m)).mul ((hJ m).pow m)

theorem metricFreeResidualBudget_polynomial (C J N : ℕ → ℝ → ℝ)
    (hC : ∀ m, HasPolynomialBound (C m)) (hJ : ∀ m, HasPolynomialBound (J m))
    (hN : ∀ m, HasPolynomialBound (N m))
    (hC1 : ∀ m x, 1 ≤ x → 1 ≤ C m x) (q m : ℕ) :
    HasPolynomialBound (fun x => metricFreeResidualBudget
      (fun r => C r x) (fun r => J r x) (fun r => N r x) q m) := by
  have he (r : ℕ) := (errorConstant_polynomial r).comp (hC r) (hC1 r)
  have hf (r : ℕ) := (fullErrorConstant_polynomial 4 r).comp (hC r) (hC1 r)
  have hb := FiniteParametrix.boundProfile_polynomial 1
    (fun r x => errorConstant r (C r x)) (fun r x => fullErrorConstant 4 r (C r x)) he hf q m
  have ht : HasPolynomialBound (fun x => tensorChartBudget m (J m x) (J (m+1) x)) := by
    unfold tensorChartBudget
    repeat first
      | exact hJ _
      | apply HasPolynomialBound.mul
      | apply HasPolynomialBound.pow
      | (apply polynomialBound_const; positivity)
  exact (ht.mul (polynomialBound_const (show (0 : ℝ) ≤ 2^m by positivity))).mul
    (hb.mul (((polynomialBound_const (Real.sqrt_nonneg 2)).mul
      (polynomialBound_const (show (0 : ℝ) ≤ 2^(m+q+1) by positivity))).mul (hN (m+q+1))))

namespace PolynomialSolveData
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}

lemma metric_freeSizeFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (N : ℕ → ℝ) (q m : ℕ) :
    c.freeSizeFactor q m (N (m+q+1)) = metricFreeSizeBudget c.C c.J N q m := by
  have hD' : c.D = fun _ => 0 := funext hD
  simp only [freeSizeFactor,metricFreeSizeBudget,tensorOrder_emptyMetricPolynomial,hD']

lemma metric_freeResidualFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (N : ℕ → ℝ) (q m : ℕ) :
    c.freeResidualFactor q m (N (m+q+1)) = metricFreeResidualBudget c.C c.J N q m := by
  have hκ : c.κ = fun r => errorConstant r (c.C r) := by
    funext r
    simp only [κ,hD r,zero_mul,max_eq_left (errorConstant_nonneg r (c.nonnegC r))]
  have hγ : c.freeInitialFactor = fun r => fullErrorConstant 4 r (c.C r) := by
    funext r
    simp only [freeInitialFactor,hD r,zero_mul,
      max_eq_left (fullErrorConstant_nonneg 4 r (c.nonnegC r))]
  simp only [freeResidualFactor,freeChartResidualFactor,metricFreeResidualBudget,hκ,hγ,
    tensorOrder_emptyMetricPolynomial,inputOrder,Nat.zero_add,Nat.mul_one]
  congr 3

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
