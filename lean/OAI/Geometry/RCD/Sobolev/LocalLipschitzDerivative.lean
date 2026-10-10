import OAI.Geometry.RCD.Sobolev.LocalLipschitzGreenPairing

namespace OAI

/-! # Almost-everywhere derivatives and finite energy on interior balls -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem local_lipschitz_derivative {n : ℕ} {f : Euclidean n → ℝ} {S R : ℝ}
    (hRS : R<S) (hf : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L f (closedBall 0 W)) :
    (∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict (ball 0 R), DifferentiableAt ℝ f x) ∧
      IntegrableOn (fun x => ‖fderiv ℝ f x‖^2) (ball 0 R) volume := by
  let W := (R+S)/2
  have hRW : R<W := by dsimp only [W]; linarith
  have hWS : W<S := by dsimp only [W]; linarith
  obtain ⟨L,hL⟩ := hf W hWS
  obtain ⟨G,hG,he⟩ := hL.extend_real
  have heq (x : Euclidean n) (hx : x∈ball (0:Euclidean n) R) : f=ᶠ[𝓝 x] G := by
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball hRW.le hx)] with y hy
    exact he (ball_subset_closedBall hy)
  have hd : ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict (ball 0 R),
      DifferentiableAt ℝ f x := by
    filter_upwards [ae_restrict_of_ae (hG.ae_differentiableAt (μ := volume)),
      ae_restrict_mem measurableSet_ball] with x hx hmem
    exact hx.congr_of_eventuallyEq (heq x hmem)
  refine ⟨hd,?_⟩
  apply (integrableOn_const (C := (L:ℝ)^2) (measure_ball_lt_top.ne)).mono'
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [(heq x hx).fderiv_eq]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hG) 2

end RegularPointCoordinates

end

end OAI
