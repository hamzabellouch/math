import OAI.Probability.SLE.Geometry.ActualFiniteBoundaryExtension
import Mathlib.Analysis.Complex.Schwarz

namespace OAI

/-! A finite continuous boundary value makes the inverse derivative small
after multiplication by the height. -/
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

lemma vertical_approach_halfPlane (x : ℝ) :
    Tendsto (fun y : ℝ => (x : ℂ)+(y : ℂ)*Complex.I)
      (𝓝[>] 0) (𝓝[upperHalfPlane] (x : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · have hc : Continuous (fun y : ℝ => (x : ℂ)+(y : ℂ)*Complex.I) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simpa [upperHalfPlane] using hy

lemma IsCapacityTwoWitness.inverse_tip_limit
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) :
    Tendsto (F T) (𝓝[upperHalfPlane] (U T : ℂ)) (𝓝 (γ T)) := by
  obtain ⟨q,hq⟩ := h.finite_real_boundary_limit T (U T)
  have he : q=γ T := tendsto_nhds_unique
    (hq.comp (vertical_approach_halfPlane (U T))) (h.2.2.2.2.2.2.2.2.2.2.2.2 T)
  simpa only [he] using hq

theorem halfPlane_boundary_derivative_vanishes
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalfPlane)
    {x : ℝ} {q : ℂ} (hl : Tendsto f (𝓝[upperHalfPlane] (x : ℂ)) (𝓝 q)) :
    Tendsto (fun y : ℝ => y*‖deriv f ((x : ℂ)+(y : ℂ)*Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.tendsto_nhdsWithin_nhds.mp hl (ε/8) (by positivity)
  refine ⟨δ/2,by positivity,?_⟩
  intro y hy hyd
  have hy0 : 0 < y := hy
  have hyδ : y < δ/2 := by simpa only [Real.dist_eq,sub_zero,abs_of_pos hy0] using hyd
  let w : ℂ := (x : ℂ)+(y : ℂ)*Complex.I
  have hw : w ∈ upperHalfPlane := by simpa [w,upperHalfPlane] using hy0
  have hdw : dist w (x : ℂ)=y := by
    simp [w,dist_eq_norm,Complex.norm_real,abs_of_pos hy0]
  have hball : ball w (y/2) ⊆ upperHalfPlane := by
    intro z hz
    have hd : ‖z-w‖ < y/2 := by simpa only [mem_ball,dist_eq_norm] using hz
    have hi := (abs_lt.mp ((Complex.abs_im_le_norm (z-w)).trans_lt hd)).1
    simp only [Complex.sub_im] at hi
    change 0 < z.im
    have hwi : w.im=y := by simp [w]
    linarith
  have hc (z : ℂ) (hz : z ∈ ball w (y/2)) : dist (f z) q < ε/8 := by
    apply hclose (hball hz)
    have ht := dist_triangle z w (x : ℂ)
    rw [hdw] at ht
    have hzdist := mem_ball.mp hz
    linarith
  have hcw : dist (f w) q < ε/8 := hc w (mem_ball_self (by positivity))
  have hm : MapsTo f (ball w (y/2)) (closedBall (f w) (ε/4)) := by
    intro z hz
    rw [mem_closedBall]
    have ht := dist_triangle (f z) q (f w)
    rw [dist_comm q (f w)] at ht
    linarith [hc z hz]
  have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hf.mono hball) hm (by positivity)
  have hb : y*‖deriv f w‖ ≤ ε/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < y/2)).mp hd
    nlinarith
  change dist (y*‖deriv f w‖) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg hy0.le (norm_nonneg _))]
  linarith

lemma IsCapacityTwoWitness.inverse_tip_derivative_vanishes
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) :
    Tendsto (fun y : ℝ => y*‖deriv (F T) ((U T : ℂ)+(y : ℂ)*Complex.I)‖)
      (𝓝[>] 0) (𝓝 0) :=
  halfPlane_boundary_derivative_vanishes (h.2.2.2.2.1 T) (h.inverse_tip_limit T)

end SLEExactGauge

end

end OAI
