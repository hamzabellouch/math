import OAI.Geometry.Perimeter.Regularity.ActualFluxWindowLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem normalWindowTest_nonneg {v : Euc n} {φ : normalPlane v → ℝ}
    (hφ : ∀ y, 0 ≤ φ y) (b : ℝ) (x : Euc n) :
    0 ≤ normalWindowTest v φ b 0 x := by
  simp only [normalWindowTest,pow_zero,mul_one]
  exact Set.indicator_nonneg (fun y _ ↦ hφ _) x

theorem weighted_positive_derivative_le_tilt (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hpφ : ∀ y, 0 ≤ φ y) {M b δ R : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    (hb : 0 ≤ b) (hR : 0 < R)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ ≤ R)
    {j : ℕ} (hj : (c1Mollifier (n := n) j).rOut < δ) :
    (∫ x, normalWindowTest v φ b 0 x *
      max (fderiv ℝ (phaseMollification E ((c1Mollifier j).normed volume)) x v) 0) ≤
      M * (orientedTilt E v (Metric.ball 0 R) / 2) := by
  let q := phaseMollification E ((c1Mollifier j).normed volume)
  let g : Euc n → ℝ := fun x ↦ max (fderiv ℝ q x v) 0
  have hg : Continuous g :=
    (((phaseMollification_contDiff hmin.1 (c1Mollifier j).contDiff_normed
      (c1Mollifier j).hasCompactSupport_normed).continuous_fderiv (by simp)).clm_apply
        continuous_const).max continuous_const
  have hi := normalWindowTest_mul_integrable hv hφ hcφ b 0 hg
  have hgi : IntegrableOn g (Metric.closedBall 0 (R-δ)) volume :=
    hg.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hMt : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM 0)
  have hdom : ∀ x, normalWindowTest v φ b 0 x * g x ≤
      (Metric.closedBall 0 (R-δ)).indicator (fun x ↦ M*g x) x := by
    intro x
    have hg0 : 0 ≤ g x := le_max_right _ _
    by_cases hx : normalWindowTest v φ b 0 x=0
    · rw [hx,zero_mul]
      exact Set.indicator_nonneg (fun x _ ↦ mul_nonneg hMt (le_max_right _ _)) _
    · have hxR : x ∈ Metric.closedBall 0 (R-δ) := by
        rw [Metric.mem_closedBall,dist_zero_right]
        have := normalWindowTest_support_norm hv φ b δ R 0 hKR hx
        linarith
      rw [Set.indicator_of_mem hxR]
      apply mul_le_mul_of_nonneg_right _ hg0
      have h := normalWindowTest_bound hM hb 0 x
      simp only [pow_zero,mul_one] at h
      rwa [Real.norm_of_nonneg (normalWindowTest_nonneg hpφ b x)] at h
  have hbound := phaseMollification_positive_derivative_le_tilt hn hmin hv
    (c1Mollifier j).contDiff_normed (c1Mollifier j).hasCompactSupport_normed
    (c1Mollifier j).nonneg_normed (c1Mollifier j).integral_normed hR
    0 (R-δ) (fun x hx ↦ c1Mollifier_translated_support (by
      rw [Metric.mem_closedBall,dist_zero_right] at hx; linarith))
  calc
    _ ≤ ∫ x, (Metric.closedBall 0 (R-δ)).indicator (fun x ↦ M*g x) x :=
      integral_mono hi (IntegrableOn.integrable_indicator (hgi.const_mul M) measurableSet_closedBall) hdom
    _ = M * ∫ x in Metric.closedBall 0 (R-δ), g x := by
      rw [integral_indicator measurableSet_closedBall,integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hMt

end RPISingularHarnack

end

end OAI
