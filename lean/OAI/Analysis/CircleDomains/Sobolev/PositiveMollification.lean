import Mathlib.Analysis.Calculus.BumpFunction.Convolution

namespace OAI

/-! Normalized smooth mollifiers preserve actual interval bounds and
constant plateaus. These are pointwise bounds on the input neighborhood. -/

open Set MeasureTheory Metric
open scoped Convolution

noncomputable section

namespace CircleDomainRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem normed_convolution_mem_Icc
    (β : ContDiffBump (0 : E)) {u : E → ℝ} (hu : AEStronglyMeasurable u μ)
    {x : E} {a b : ℝ} (hb : ∀y ∈ ball x β.rOut, u y ∈ Icc a b) :
    ((β.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) ∈ Icc a b := by
  have hab : a ≤ b := (hb x (mem_ball_self β.rOut_pos)).1.trans
    (hb x (mem_ball_self β.rOut_pos)).2
  have hr : 0 ≤ (b - a) / 2 := by linarith
  have hdist : ∀y ∈ ball x β.rOut, dist (u y) ((a + b) / 2) ≤ (b - a) / 2 := by
    intro y hy
    obtain ⟨hya, hyb⟩ := hb y hy
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have h := dist_convolution_le hr (β.support_normed_eq.subset)
    β.nonneg_normed β.integral_normed hu hdist
  rw [Real.dist_eq, abs_le] at h
  constructor <;> linarith [h.1, h.2]

theorem normed_convolution_eq_of_constant
    [HasContDiffBump E] (β : ContDiffBump (0 : E)) {u : E → ℝ} {x : E} {c : ℝ}
    (hc : ∀y ∈ ball x β.rOut, u y = c) :
    ((β.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) x) = c := by
  rw [β.normed_convolution_eq_right (fun y hy => (hc y hy).trans
    (hc x (mem_ball_self β.rOut_pos)).symm)]
  exact hc x (mem_ball_self β.rOut_pos)

end CircleDomainRigidity

end

end OAI
