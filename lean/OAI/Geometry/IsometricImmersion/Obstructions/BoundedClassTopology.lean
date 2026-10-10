import OAI.Geometry.IsometricImmersion.Comparison.BoundedClassApproximation
import Mathlib.Topology.GDelta.Basic

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow

theorem boundedHeightClass_nonempty_parameters
    {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    (hclass : (boundedHeightClass g0 kappa M q0).Nonempty) :
    0 < M ∧ |(q0 : ℝ)| < 1/20 := by
  obtain ⟨eta,z,hz,hcenter⟩ := hclass
  exact ⟨hz.1,boundedHeightClass_label_abs_lt ⟨eta,z,hz,hcenter⟩⟩

theorem boundedHeightClass_closure_parameters
    {g0 : MetricField} {kappa : ℝ} {M : ℕ} {q0 : ℚ}
    {eta : metricPatchSet g0 kappa}
    (heta : eta ∈ closure (boundedHeightClass g0 kappa M q0)) :
    0 < M ∧ |(q0 : ℝ)| < 1/20 :=
  boundedHeightClass_nonempty_parameters (Set.Nonempty.of_closure ⟨eta,heta⟩)

theorem bounded_class_open_closure_pulse_family_at_radius
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (M : ℕ) (q0 : ℚ)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O)
    {etaStar : metricPatchSet g0 kappa} (hStar : etaStar ∈ O)
    (hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0))
    {r : ℝ} (hr : 0 < r) (hLr : boundedClassWidth kappa M*r ≤ 1/20) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop, 0 < tau ∧
        ∃ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z ∧
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-(q0 : ℝ)| ≤
            1/(100*boundedClassWidth kappa M) ∧
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun x => perturbedMetric g0 eta.val x i j-
              testMetric (perturbedMetric g0 etaStar.val) (q0 : ℝ)
                (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) x i j) p‖ ≤
                  metricApproximationAccuracy tau) := by
  have hparams := boundedHeightClass_closure_parameters (hOclosure hStar)
  let a := boundedClassWidth kappa M*r/16
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  have hax : a ≤ 1/10 := by
    dsimp only [a]
    linarith
  have hq : |(q0 : ℝ)| *a < 1/10 := by
    have hm := mul_le_mul hparams.2.le hax ha.le (by norm_num : (0 : ℝ) ≤ 1/20)
    norm_num at hm
    linarith
  obtain ⟨N,hN,hfamily⟩ := exists_N_before_delta_eventually_bounded_height_approximation
    hg0 hV hSV M q0 hO hStar hOclosure a ha hax hq
  refine ⟨N,hN,?_⟩
  intro delta hdelt
  filter_upwards [hfamily delta hdelt] with tau htau
  obtain ⟨eta,z,hclass,hcenter,_,_,hC⟩ := htau.2
  exact ⟨htau.1,eta,z,hclass,hcenter.le,fun i j k hk p _ => hC i j k hk p⟩

end SmoothLocal.Perturbation

end

end OAI
