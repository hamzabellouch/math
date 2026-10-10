import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

namespace OAI

/-! Smooth approximation of compact C1 coordinate functions, controlling
both the value and the actual first derivative. -/
noncomputable section
open Set MeasureTheory Metric
open scoped Convolution Pointwise ContDiff
namespace CubicFirstMoment

local instance cubicThetaSmoothing_haar :
    (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

def cubicThetaCoordinateSmooth (φ : ContDiffBump (0 : ℂ × ℝ))
    (g : ℂ × ℝ → ℂ) : ℂ × ℝ → ℂ :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

lemma cubicThetaCoordinateSmooth_contDiff (φ : ContDiffBump (0 : ℂ × ℝ))
    {g : ℂ × ℝ → ℂ} (hg : Continuous g) :
    ContDiff ℝ ∞ (cubicThetaCoordinateSmooth φ g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hg.locallyIntegrable

lemma cubicThetaCoordinateSmooth_compact (φ : ContDiffBump (0 : ℂ × ℝ))
    {g : ℂ × ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (cubicThetaCoordinateSmooth φ g) :=
  φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg

lemma cubicThetaCoordinateSmooth_support (φ : ContDiffBump (0 : ℂ × ℝ))
    {g : ℂ × ℝ → ℂ} (hg : HasCompactSupport g) :
    tsupport (cubicThetaCoordinateSmooth φ g) ⊆
      closedBall (0 : ℂ × ℝ) φ.rOut + tsupport g := by
  apply closure_minimal
  · exact (support_convolution_subset _).trans
      (add_subset_add (by rw [φ.support_normed_eq]; exact ball_subset_closedBall) subset_closure)
  · exact (isCompact_closedBall _ _ |>.add hg).isClosed

lemma cubicThetaCoordinateSmooth_fderiv (φ : ContDiffBump (0 : ℂ × ℝ))
    {g : ℂ × ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (x : ℂ × ℝ) :
    fderiv ℝ (cubicThetaCoordinateSmooth φ g) x =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ g) x := by
  have h := hc.hasFDerivAt_convolution_right (μ:=volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    ((φ.continuous_normed (μ:=volume)).locallyIntegrable (μ:=volume)) hg x
  unfold cubicThetaCoordinateSmooth
  rw [h.fderiv]
  congr 1

lemma cubicThetaCoordinateSmooth_exists {g : ℂ × ℝ → ℂ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) {ε ρ : ℝ}
    (hε : 0<ε) (hρ : 0<ρ) :
    ∃ φ : ContDiffBump (0 : ℂ × ℝ), φ.rOut<ρ ∧
      (∀ x, ‖cubicThetaCoordinateSmooth φ g x-g x‖≤ε) ∧
      (∀ x, ‖fderiv ℝ (cubicThetaCoordinateSmooth φ g) x-fderiv ℝ g x‖≤ε) := by
  have hu := hc.uniformContinuous_of_continuous hg.continuous
  have hdu := (hc.fderiv ℝ).uniformContinuous_of_continuous (hg.continuous_fderiv one_ne_zero)
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  obtain ⟨δ',hδ',hd'⟩ := Metric.uniformContinuous_iff.mp hdu ε hε
  let r := min ρ (min δ δ') / 2
  have hr : 0<r := half_pos (lt_min hρ (lt_min hδ hδ'))
  let φ : ContDiffBump (0 : ℂ × ℝ) := ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  have hrρ : r<ρ := (half_lt_self (lt_min hρ (lt_min hδ hδ'))).trans_le (min_le_left _ _)
  have hrδ : r<δ := (half_lt_self (lt_min hρ (lt_min hδ hδ'))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrδ' : r<δ' := (half_lt_self (lt_min hρ (lt_min hδ hδ'))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨φ,hrρ,?_,?_⟩
  · intro x
    rw [← dist_eq_norm]
    exact φ.dist_normed_convolution_le (μ:=volume) (g:=g) hg.continuous.aestronglyMeasurable
      (fun y hy => (hd ((mem_ball.mp hy).trans hrδ)).le)
  · intro x
    rw [cubicThetaCoordinateSmooth_fderiv φ hg hc]
    rw [← dist_eq_norm]
    exact φ.dist_normed_convolution_le (μ:=volume) (g:=fderiv ℝ g)
      (hg.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (fun y hy => (hd' ((mem_ball.mp hy).trans hrδ')).le)

end CubicFirstMoment

end

end OAI
