import OAI.Geometry.IsometricImmersion.Comparison.ClosureMetricApproximation
import OAI.Geometry.IsometricImmersion.Pulses.PulseNeighborhoodAdapters

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

def metricApproximationAccuracy (tau : ℕ) : ℝ := 1 / ((tau : ℝ)^tau)

theorem metricApproximationAccuracy_pos {tau : ℕ} (htau : 0 < tau) :
    0 < metricApproximationAccuracy tau :=
  one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr htau) tau)

theorem relative_closure_exists_metric_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U)
    {A : Set (metricPatchSet g0 kappa)} {theta : metricPatchSet g0 kappa}
    (hclosure : theta ∈ closure A) (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : metricPatchSet g0 kappa, eta ∈ A ∧
      SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
      (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa / 2) ∧
      (∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
          perturbedMetric g0 theta.val x) p‖ ≤ epsilon) ∧
      (∀ i j : Fin 2, ∀ k ≤ n, ∀ p : Coord,
        ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
          perturbedMetric g0 theta.val x i j) p‖ ≤ epsilon) := by
  obtain ⟨eta, heta, hT, hC⟩ := closure_exists_metric_jet_approximation
    (Subtype.val : metricPatchSet g0 kappa → SymmetricPerturbation) continuous_subtype_val
    g0 hclosure n hepsilon
  exact ⟨eta, heta, perturbedMetric_smoothPositiveOn hg0 eta.val eta.property.1,
    eta.property.2, hT, hC⟩

theorem exists_N_before_delta_eventually_class_approximation
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {A O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure A)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ eta : metricPatchSet g0 kappa, eta ∈ A ∧
          SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
          (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa / 2) ∧
          (∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
              testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x) p‖ ≤
                metricApproximationAccuracy tau) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
              testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x i j) p‖ ≤
                metricApproximationAccuracy tau) := by
  obtain ⟨N, hN, hpulse⟩ := exists_N_before_delta_eventually_relative_metric_neighborhood
    hg0 hU hSU hO hStar q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hdelta
  filter_upwards [hpulse delta hdelta] with tau htau
  have hpositive : 0 < tau := by
    have hh : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htau.1
    exact_mod_cast hh
  obtain ⟨theta, hthetaO, hthetaEq, hthetaPositive, hthetaCentral⟩ := htau.2
  obtain ⟨eta, heta, hmetric, hcentral, hT, hC⟩ :=
    relative_closure_exists_metric_approximation hg0 (hOclosure hthetaO) tau
      (metricApproximationAccuracy_pos hpositive)
  refine ⟨hpositive, eta, heta, hmetric, hcentral, ?_, ?_⟩
  · simpa only [hthetaEq] using hT
  · simpa only [hthetaEq] using hC

theorem exists_N_before_delta_class_metric_family
    {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {A O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure A)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∃ tau0 : ℕ, 1 ≤ tau0 ∧ ∃ eta : ℕ → metricPatchSet g0 kappa,
        ∀ tau : ℕ, tau0 ≤ tau → eta tau ∈ A ∧
          SmoothPositiveOn (perturbedMetric g0 (eta tau).val) U ∧
          (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 (eta tau).val) p < -kappa / 2) ∧
          (∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (eta tau).val x -
              testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x) p‖ ≤
                metricApproximationAccuracy tau) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p : Coord,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 (eta tau).val x i j -
              testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x i j) p‖ ≤
                metricApproximationAccuracy tau) := by
  classical
  obtain ⟨N, hN, happrox⟩ := exists_N_before_delta_eventually_class_approximation
    hg0 hU hSU hO hStar hOclosure q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hdelta
  obtain ⟨tauBase, hbase⟩ := eventually_atTop.mp (happrox delta hdelta)
  let tau0 := max 1 tauBase
  have hchoose : ∀ tau : ℕ, ∃ eta : metricPatchSet g0 kappa,
      tau0 ≤ tau → eta ∈ A ∧ SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
        (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa / 2) ∧
        (∀ k ≤ tau, ∀ p : Coord,
          ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x -
            testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x) p‖ ≤
              metricApproximationAccuracy tau) ∧
        (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p : Coord,
          ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j -
            testMetric (perturbedMetric g0 etaStar.val) q0 a N delta (tau : ℝ) x i j) p‖ ≤
              metricApproximationAccuracy tau) := by
    intro tau
    by_cases htau : tau0 ≤ tau
    · obtain ⟨eta, heta⟩ := (hbase tau ((le_max_right 1 tauBase).trans htau)).2
      exact ⟨eta, fun _ => heta⟩
    · exact ⟨etaStar, fun h => False.elim (htau h)⟩
  choose eta heta using hchoose
  exact ⟨tau0, le_max_left _ _, eta, heta⟩

end SmoothLocal.Pulse

end

end OAI
