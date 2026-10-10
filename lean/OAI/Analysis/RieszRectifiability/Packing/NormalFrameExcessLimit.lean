import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess
import OAI.Analysis.RieszRectifiability.Limits.MovingAffineGraphLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Topology

theorem moving_normal_frame_squaredExcess_ratio_tendsto_zero {n q d : ℕ}
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (center : Ambient d) (r : ℝ) (hr : 0 ≤ r) (a : ℕ → Ambient d)
    (L : ℕ → Ambient n →ₗᵢ[ℝ] Ambient d) (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (horth : ∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0)
    (hsplit : ∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
      N j ((N j).toContinuousLinearMap.adjoint y) = y)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (b : Ambient q) (B : Ambient d →L[ℝ] Ambient q)
    (hraw : ∀ j, Integrable (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2) ((σ j).restrict (ball center r)))
    (C : ℝ) (hC : ∀ j, (∫ x, ‖normalizedNormalHeight (a j) (N j) (δ j) x‖ ^ 2 ∂(σ j).restrict (ball center r)) ≤ C)
    (herr : ∀ j, Integrable
      (fun x => ‖normalizedNormalHeight (a j) (N j) (δ j) x - (b + B x)‖ ^ 2) ((σ j).restrict (ball center r)))
    (hstrong : Tendsto (fun j => ∫ x,
      ‖normalizedNormalHeight (a j) (N j) (δ j) x - (b + B x)‖ ^ 2 ∂(σ j).restrict (ball center r)) atTop (𝓝 0)) :
    Tendsto (fun j => squaredExcess n (σ j) center r / δ j ^ 2) atTop (𝓝 0) := by
  obtain ⟨S, hS, _hi, hlim⟩ := moving_affine_graph_distance_tendsto_zero
    (fun j => (σ j).restrict (ball center r)) a L N horth hsplit δ hδ hδlim
    b B hraw C hC herr hstrong
  exact squaredExcess_ratio_tendsto_zero_of_planes n σ center r hr S hS δ hlim

end

end RieszRectifiability

end OAI
