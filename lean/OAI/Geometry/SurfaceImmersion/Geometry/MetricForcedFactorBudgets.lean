import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMetricForcedBudgets
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveFactors
import OAI.Geometry.Immersion.ClosedSurface.QuadraticSupport

namespace OAI

/-! Polynomial geometric factors and the number of actual quadratic labels. -/
noncomputable section
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.RealModes

theorem card_quadraticLabel_le (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Fintype.card (QuadraticLabel ι) ≤ Fintype.card ι + 2*(Fintype.card ι)^2 := by
  change Fintype.card (ι ⊕ (Σ i : ι, {j : ι // j ≠ i} × Bool)) ≤ _
  rw [Fintype.card_sum,Fintype.card_sigma]
  apply Nat.add_le_add_left
  calc
    (∑ i : ι, Fintype.card ({j : ι // j ≠ i} × Bool)) ≤
        ∑ _i : ι, Fintype.card ι*2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [Fintype.card_prod,Fintype.card_bool]
      exact Nat.mul_le_mul_right 2 (Fintype.card_subtype_le _)
    _ = 2*(Fintype.card ι)^2 := by simp; ring

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open SmallModes RealModes
variable {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : TopologicalSpace.Compacts Base} {τ : ℝ} {s : ℝ≥0}

lemma metric_sizeFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (q m : ℕ) :
    c.sizeFactor q m = metricForcedSizeBudget c.C c.J (fun _ => 1) q m := by
  have hD' : c.D = (fun _ => 0) := funext hD
  simp only [sizeFactor,metricForcedSizeBudget,tensorOrder_emptyMetricPolynomial,hD',mul_one]
  ring

lemma metric_residualFactor_eq (c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (hD : ∀ m, c.D m = 0) (q m : ℕ) :
    c.residualFactor q m = metricForcedResidualBudget c.C c.J (fun _ => 1) q m := by
  have hκ : c.κ = fun r => errorConstant r (c.C r) := by
    funext r
    simp only [κ,hD r,zero_mul,max_eq_left (errorConstant_nonneg r (c.nonnegC r))]
  simp only [residualFactor,metricForcedResidualBudget,hκ,tensorOrder_emptyMetricPolynomial,
    Nat.zero_add,mul_one]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
