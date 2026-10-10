import OAI.Geometry.NodalSets.Charts.LocalMetricChart

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem common_local_smooth_extension {U : Set Coord} (hU : IsOpen U)
    (f : Coord → F) (hf : ContDiffOn ℝ ∞ f U) {y : Coord} (hy : y ∈ U) :
    ∃ (r : ℝ) (G : Coord → F), 0 < r ∧ ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ U ∧ Metric.closedBall y r ⊆ U ∧
      (∀ x ∈ Metric.ball y r, G x = f x) ∧
      ∀ x ∈ Metric.ball y r, G =ᶠ[𝓝 x] f := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  let beta : ContDiffBump y := ⟨r/4, r/2, by positivity, by linarith⟩
  have hsupport : tsupport beta ⊆ U := by
    rw [beta.tsupport_eq]
    intro x hx
    apply hball
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    dsimp [beta] at hx'
    linarith
  let G := fun x ↦ beta x • f x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport beta
    · exact beta.contDiff.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds (hsupport hx)))
    · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      have hn : (tsupport beta)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
      filter_upwards [hn] with z hz
      simp [G, image_eq_zero_of_notMem_tsupport hz]
  have hsub : tsupport G ⊆ tsupport beta := by
    apply closure_mono
    intro x hx
    change beta x ≠ 0
    intro hz
    exact hx (by simp [G, hz])
  have heq : ∀ x ∈ Metric.ball y (r/4), G x = f x := by
    intro x hx
    have hb : beta x = 1 := beta.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [G, hb]
  refine ⟨r/4, G, by positivity, hG,
    beta.hasCompactSupport.of_isClosed_subset isClosed_closure hsub,
    hsub.trans hsupport, ?_, heq, ?_⟩
  · intro x hx
    apply hball
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    linarith
  · intro x hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact heq z hz

end
end Yau.Geometry

end OAI
