import OAI.Geometry.Perimeter.Regularity.PerimeterMomentLimit
import OAI.Geometry.Perimeter.Regularity.NormalWindowTest

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem c1Mollifier_translated_support {j : ℕ} {x : Euc n} {R : ℝ}
    (hx : ‖x‖+(c1Mollifier (n := n) j).rOut < R) :
    tsupport (fun y ↦ (c1Mollifier j).normed volume (x-y)) ⊆ Metric.ball 0 R := by
  intro y hy
  have hs : x-y ∈ tsupport ((c1Mollifier j).normed volume) :=
    tsupport_comp_subset_preimage ((c1Mollifier j).normed volume)
      (continuous_const.sub continuous_id) hy
  rw [(c1Mollifier j).tsupport_normed_eq] at hs
  have hnorm : ‖x-y‖ ≤ (c1Mollifier (n := n) j).rOut := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hs
  rw [Metric.mem_ball,dist_zero_right]
  have h := norm_sub_le x (x-y)
  rw [sub_sub_cancel] at h
  linarith

theorem normalWindowTest_ae_continuousAt {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {v : Euc n}
    {φ : normalPlane v → ℝ} (hφ : Continuous φ) {b R : ℝ} (m : ℕ)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| < b) :
    ∀ᵐ x ∂(perimeterMeasure E).restrict (Metric.ball 0 R),
      ContinuousAt (normalWindowTest v φ b m) x := by
  let := perimeterMeasure_locallyFinite E hmin.2.1
  have hs : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
    rw [← perimeterMeasure_support]
    exact (perimeterMeasure E).support_mem_ae
  filter_upwards [ae_restrict_of_ae hs,ae_restrict_mem measurableSet_ball] with x hx hxR
  exact normalWindowTest_continuousAt hφ m (hh x ⟨hx,hxR⟩)

theorem actual_normal_flux_window_tendsto (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖ = 1) {φ : normalPlane v → ℝ}
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    {b δ R : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) (hR : 0 < R) (m : ℕ)
    (hKR : ∀ y ∈ tsupport φ, ‖y‖+b+δ ≤ R)
    (hh : ∀ x ∈ perimeterSupport E ∩ Metric.ball 0 R, |inner ℝ v x| < b) :
    Tendsto (fun j ↦ ∫ x, normalWindowTest v φ b m x *
      (-fderiv ℝ (phaseMollification E ((c1Mollifier j).normed volume)) x v)) atTop
      (𝓝 (∫ x in Metric.ball 0 R, normalWindowTest v φ b m x *
        inner ℝ (approximateNormal E x) v ∂perimeterMeasure E)) := by
  let μ := (perimeterMeasure E).restrict (Metric.ball 0 R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ,perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 0 R hR⟩
  let f : Euc n → ℝ := fun x ↦ inner ℝ (approximateNormal E x) v
  have hf : Integrable f μ := (integrable_const (1:ℝ)).mono'
    (((measurable_approximateNormal hmin.1).inner measurable_const).aestronglyMeasurable)
    (ae_of_all _ fun x ↦ by
      change ‖inner ℝ (approximateNormal E x) v‖ ≤ 1
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by
        rw [hv,mul_one]; exact approximateNormal_norm_le_one E x))
  obtain ⟨M,hM⟩ := hcφ.exists_bound_of_continuous hφ
  have ht := weak_c1_convolution_tendsto_of_ae_continuous μ hf
    (normalWindowTest_measurable hφ b m) (normalWindowTest_bound hM hb m)
    (normalWindowTest_ae_continuousAt hmin hφ m hh)
  apply ht.congr'
  have he : ∀ᶠ j in atTop, (c1Mollifier (n := n) j).rOut < δ :=
    c1Mollifier_radius_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [he] with j hj
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  by_cases hx : normalWindowTest v φ b m x=0
  · simp only [hx,zero_mul]
  · have hs := c1Mollifier_translated_support (j := j) (x := x)
      (R := R) (by have h := normalWindowTest_support_norm hv φ b δ R m hKR hx; linarith)
    rw [phaseMollification_fderiv hn hmin (c1Mollifier j).contDiff_normed
      (c1Mollifier j).hasCompactSupport_normed x v hR hs,neg_neg]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun y ↦ mul_comm _ _

end RPISingularHarnack

end

end OAI
