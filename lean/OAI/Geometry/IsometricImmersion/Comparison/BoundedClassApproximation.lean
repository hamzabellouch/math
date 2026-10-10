import OAI.Geometry.IsometricImmersion.Immersions.BoundedHeightClasses
import OAI.Geometry.IsometricImmersion.Comparison.PulseClosureApproximation

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse

theorem boundedHeightClass_closure_exists_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (M : ℕ) (q0 : ℚ)
    {theta : metricPatchSet g0 kappa}
    (hclosure : theta ∈ closure (boundedHeightClass g0 kappa M q0))
    (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
      BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
      |hessianQuotient (perturbedMetric g0 eta.val) z 0 - (q0 : ℝ)| <
        1 / (100 * boundedClassWidth kappa M) ∧
      SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
      (∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
          perturbedMetric g0 theta.val x) p‖ ≤ epsilon) ∧
      (∀ i j : Fin 2, ∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
          perturbedMetric g0 theta.val x i j) p‖ ≤ epsilon) := by
  obtain ⟨eta, heta, hpositive, _, hT, hC⟩ :=
    relative_closure_exists_metric_approximation hg0 hclosure n hepsilon
  obtain ⟨z, hz, hlabel⟩ := heta
  exact ⟨eta, z, hz, hlabel, hpositive, hT, hC⟩

theorem exists_N_before_delta_eventually_bounded_height_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (M : ℕ) (q0 : ℚ)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0))
    (a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |(q0 : ℝ)| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
          |hessianQuotient (perturbedMetric g0 eta.val) z 0 - (q0 : ℝ)| <
            1 / (100 * boundedClassWidth kappa M) ∧
          SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
          (∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ) a N delta (tau : ℝ) x) p‖ ≤
                metricApproximationAccuracy tau) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ) a N delta (tau : ℝ) x i j) p‖ ≤
                metricApproximationAccuracy tau) := by
  obtain ⟨N, hN, happrox⟩ := exists_N_before_delta_eventually_class_approximation
    hg0 hU hSU hO hStar hOclosure (q0 : ℝ) a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hdelta
  filter_upwards [happrox delta hdelta] with tau htau
  obtain ⟨eta, ⟨z, hz, hlabel⟩, hpositive, _, hT, hC⟩ := htau.2
  exact ⟨htau.1, eta, z, hz, hlabel, hpositive, hT, hC⟩

end SmoothLocal.Perturbation

end

end OAI
