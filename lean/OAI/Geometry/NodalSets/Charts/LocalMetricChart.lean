import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import OAI.Geometry.NodalSets.Spectral.NormalOrthonormalChart

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem local_metric_extension {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u) {y : Coord} (hy : y ∈ U) :
    ∃ G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ,
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ G =ᶠ[𝓝 y] g ∧
      ∀ x u v, G x u v = G x v u := by
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
  let G := fun x ↦ beta x • g x
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport beta
    · exact beta.contDiff.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds (hsupport hx)))
    · apply (contDiffAt_const (c := (0 : Coord →L[ℝ] Coord →L[ℝ] ℝ))).congr_of_eventuallyEq
      have hn : (tsupport beta)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
      filter_upwards [hn] with z hz
      simp [G, image_eq_zero_of_notMem_tsupport hz]
  have hcompact : HasCompactSupport G := by
    apply beta.hasCompactSupport.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    change beta x ≠ 0
    intro hz
    exact hx (by simp [G, hz])
  refine ⟨G, hG, hcompact, ?_, ?_⟩
  · filter_upwards [beta.eventuallyEq_one] with x hx
    simp [G, hx]
  · intro x u v
    by_cases hx : x ∈ tsupport beta
    · change beta x * g x u v = beta x * g x v u
      rw [hs x (hsupport hx)]
    · simp [G, image_eq_zero_of_notMem_tsupport hx]

theorem exists_local_orthonormal_normal_chart {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u) {y : Coord} (hy : y ∈ U)
    (hp : ∀ v : Coord, v ≠ 0 → 0 < g y v v) :
    ∃ F : OpenPartialHomeomorph Coord Coord,
      0 ∈ F.source ∧ F 0 = y ∧ ContDiff ℝ ∞ (F : Coord → Coord) ∧
      ContDiffAt ℝ ∞ F.symm y ∧ (∀ᶠ x in 𝓝 0, F x ∈ U) ∧
      (∀ i j : Fin 4, pullbackMetric g F 0 (Pi.single i 1) (Pi.single j 1) =
        if i = j then 1 else 0) ∧
      ∀ u v, fderiv ℝ (fun x ↦ pullbackMetric g F x u v) 0 = 0 := by
  obtain ⟨G, hG, _, heq, hGs⟩ := local_metric_extension hU g hg hs hy
  have hGy : G y = g y := heq.self_of_nhds
  obtain ⟨F, hF0, hFy, hFs, hFi, hM0, hM1⟩ := exists_orthonormal_normal_chart G hG hGs y
    (by simpa [hGy] using hp)
  have hFt : Tendsto F (𝓝 0) (𝓝 y) := by simpa only [ContinuousAt, hFy] using hFs.continuous.continuousAt (x := 0)
  have heF : G ∘ F =ᶠ[𝓝 0] g ∘ F := heq.comp_tendsto hFt
  refine ⟨F, hF0, hFy, hFs, hFi, hFt.eventually (hU.mem_nhds hy), ?_, ?_⟩
  · intro i j
    simpa [pullbackMetric, hFy, hGy] using hM0 i j
  · intro u v
    have he : (fun x ↦ pullbackMetric G F x u v) =ᶠ[𝓝 0]
        (fun x ↦ pullbackMetric g F x u v) := by
      filter_upwards [heF] with x hx
      simp only [Function.comp_apply] at hx
      simp only [pullbackMetric, hx]
    rw [← he.fderiv_eq]
    exact hM1 u v

end
end Yau.Geometry

end OAI
