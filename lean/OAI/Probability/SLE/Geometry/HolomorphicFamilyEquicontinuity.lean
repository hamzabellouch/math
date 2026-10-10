import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! Local compact bounds give a common continuity modulus for the
holomorphic half-plane families used in the normal-family argument. -/
noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

lemma holomorphic_halfPlane_family_equicontinuous
    (f : ℕ → ℂ → ℂ) (hf : ∀ n, DifferentiableOn ℂ (f n) upperHalfPlane)
    (hb : ∀ K : Set ℂ, IsCompact K → K⊆upperHalfPlane →
      ∃ C : ℝ, ∀ n, ∀ z∈K, ‖f n z‖≤C) :
    Equicontinuous (fun n (z : upperHalfPlane) => f n z) := by
  intro x
  obtain ⟨R,hR,hRH⟩ := Metric.nhds_basis_ball.mem_iff.mp (isOpen_upperHalfPlane.mem_nhds x.property)
  let r := R/3
  have hr : 0<r := by dsimp [r]; positivity
  have hKH : closedBall x.1 (2*r) ⊆ upperHalfPlane := by
    intro z hz
    apply hRH
    rw [mem_ball]
    have hzr := mem_closedBall.mp hz
    dsimp [r] at hzr
    linarith
  obtain ⟨C,hC⟩ := hb (closedBall x.1 (2*r)) (isCompact_closedBall _ _) hKH
  have hder (n : ℕ) (z : ℂ) (hz : z∈ball x.1 r) : ‖deriv (f n) z‖≤C/r := by
    have hball : closedBall z r ⊆ closedBall x.1 (2*r) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      have hzx := mem_ball.mp hz
      have htri := dist_triangle w z x.1
      linarith
    rw [← Complex.cderiv_eq_deriv isOpen_upperHalfPlane (hf n) hr (hball.trans hKH)]
    exact Complex.norm_cderiv_le hr (fun w hw => hC n w (hball (sphere_subset_closedBall hw)))
  apply Metric.equicontinuousAt_of_continuity_modulus
    (fun y : upperHalfPlane => (C/r)*dist x.1 y.1)
  · have hc : Continuous (fun y : upperHalfPlane => (C/r)*dist x.1 y.1) := by fun_prop
    simpa using hc.tendsto x
  · have hn : {y : upperHalfPlane | y.1∈ball x.1 r} ∈ 𝓝 x :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds x.1 hr)
    filter_upwards [hn] with y hy n
    have hrH : ball x.1 r ⊆ upperHalfPlane :=
      (ball_subset_ball (show r≤2*r by linarith)).trans (ball_subset_closedBall.trans hKH)
    have h := (convex_ball x.1 r).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hf n).differentiableAt (isOpen_upperHalfPlane.mem_nhds (hrH hz)))
      (hder n) (mem_ball_self hr) hy
    simpa only [dist_eq_norm,norm_sub_rev] using h

end SLEExactGauge

end

end OAI
