import OAI.Geometry.NodalSets.Elliptic.CommonLocalExtension

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem common_positive_metric_extension {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v) {y : Coord} (hy : y ∈ U) :
    ∃ (r : ℝ) (G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ),
      0 < r ∧ ContDiff ℝ ∞ G ∧
      (∀ x u v, G x u v = G x v u) ∧
      (∀ x v, v ≠ 0 → 0 < G x v v) ∧
      Metric.closedBall y r ⊆ U ∧
      (∀ x ∈ Metric.ball y r, G x = g x) ∧
      ∀ x ∈ Metric.ball y r, G =ᶠ[𝓝 x] g := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hy)
  let beta : ContDiffBump y := ⟨r/4,r/2,by positivity,by linarith⟩
  have hsupport : tsupport beta ⊆ U := by
    rw [beta.tsupport_eq]
    intro x hx
    apply hball
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_closedBall.mp hx
    dsimp [beta] at hx'
    linarith
  let G := fun x ↦ beta x • g x + (1-beta x) • g y
  have hGs : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport beta
    · exact (beta.contDiff.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hsupport hx)))).add
        ((contDiffAt_const.sub beta.contDiff.contDiffAt).smul contDiffAt_const)
    · apply (contDiffAt_const (c := g y)).congr_of_eventuallyEq
      have hn : (tsupport beta)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
      filter_upwards [hn] with z hz
      simp [G, image_eq_zero_of_notMem_tsupport hz]
  have heq : ∀ x ∈ Metric.ball y (r/4), G x = g x := by
    intro x hx
    have hb : beta x = 1 := beta.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    simp [G,hb]
  refine ⟨r/4,G,by positivity,hGs,?_,?_,?_,heq,?_⟩
  · intro x u v
    by_cases hx : x ∈ tsupport beta
    · change beta x*g x u v+(1-beta x)*g y u v = beta x*g x v u+(1-beta x)*g y v u
      rw [hs x (hsupport hx),hs y hy]
    · simp [G,image_eq_zero_of_notMem_tsupport hx,hs y hy]
  · intro x v hv
    by_cases hx : x ∈ tsupport beta
    · have h1 := hp x (hsupport hx) v hv
      have h2 := hp y hy v hv
      have hb0 : 0 ≤ beta x := beta.nonneg
      have hb1 : beta x ≤ 1 := beta.le_one
      change 0 < beta x*g x v v+(1-beta x)*g y v v
      by_cases hb : beta x = 0
      · simpa [hb] using h2
      · have ha : 0 < beta x := lt_of_le_of_ne hb0 (Ne.symm hb)
        have hleft := mul_pos ha h1
        have hright := mul_nonneg (sub_nonneg.mpr hb1) h2.le
        linarith
    · simpa [G,image_eq_zero_of_notMem_tsupport hx] using hp y hy v hv
  · intro x hx
    apply hball
    apply Metric.mem_ball.mpr
    have hh := Metric.mem_closedBall.mp hx
    linarith
  · intro x hx
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact heq z hz

end
end Yau.Geometry

end OAI
