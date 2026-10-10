import OAI.Geometry.NodalSets.Charts.LocalMetricJetContinuityLemmas
import OAI.Geometry.NodalSets.Charts.MetricCoercivity
import OAI.Geometry.NodalSets.Elliptic.CompactFreezing

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

def corrugationOldSlope (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S : Coord → ℝ) (y : Coord) : ℝ :=
  Real.sqrt (g y (metricGradient g S y) (metricGradient g S y))

lemma corrugationOldSlope_positive (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S : Coord → ℝ) (y : Coord) (hp : ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : metricGradient g S y ≠ 0) : 0 < corrugationOldSlope g S y :=
  Real.sqrt_pos.mpr (hp _ hn)

lemma corrugationOldSlope_continuousOn (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S : Coord → ℝ) {U : Set Coord} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) :
    ContinuousOn (corrugationOldSlope g S) U := by
  intro y hy
  have hg' := hg.contDiffAt (hU.mem_nhds hy)
  have hS' := hS.contDiffAt (hU.mem_nhds hy)
  have hgrad : ContinuousAt (metricGradient g S) y :=
    localMetricGradient_continuousAt g S y hg'.continuousAt hS' (hp y hy)
  exact (Real.continuous_sqrt.continuousAt.comp
    ((hg'.continuousAt.clm_apply hgrad).clm_apply hgrad)).continuousWithinAt

lemma corrugationOldSlope_compact_bounds
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∃ B : ℝ, 0 < B ∧
      ∀ y ∈ D, m ≤ corrugationOldSlope g S y ∧ corrugationOldSlope g S y ≤ B := by
  exact compact_positive_bounds hD _
    ((corrugationOldSlope_continuousOn g S hU hg hS hp).mono hDU)
    (fun y hy ↦ corrugationOldSlope_positive g S y (hp y (hDU hy)) (hn y hy))

lemma compact_metric_comparison (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {D : Set Coord} (hD : IsCompact D) (hg : ContinuousOn g D)
    (hp : ∀ y ∈ D, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℝ, 0 < M ∧
      ∀ y ∈ D, ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  obtain ⟨c,hc,M,hM,hb⟩ := uniform_metric_coercivity (fun y : D ↦ g y)
    hg.domRestrict (fun y v hv ↦ hp y y.property v hv)
  exact ⟨c,hc,M,hM,fun y hy ↦ hb ⟨y,hy⟩⟩

lemma compact_connection_bound (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {D U : Set Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) :
    ∃ G : ℝ, 0 < G ∧ ∀ y ∈ D, ‖metricConnection (g y) (fderiv ℝ g y)‖ ≤ G := by
  have hc : ContinuousOn (fun y ↦ metricConnection (g y) (fderiv ℝ g y)) D := by
    intro y hy
    have hg' := hg.contDiffAt (hU.mem_nhds (hDU hy))
    exact (metric_connection_continuousAt g (fderiv ℝ g) y hg'.continuousAt
      (hg'.continuousAt_fderiv (by simp)) (hp y (hDU hy))).continuousWithinAt
  obtain ⟨G,hG,hb⟩ := (hD.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  exact ⟨G,hG,fun y hy ↦ hb _ ⟨y,hy,rfl⟩⟩

lemma corrugation_frozen_axis_differential
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ) (y : Coord)
    (hp : ∀ v, v ≠ 0 → 0 < g y v v) (hn : metricGradient g S y ≠ 0)
    (e : Coord ≃L[ℝ] Coord)
    (he : e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y) :
    fderiv ℝ S y (e (Pi.single 0 1)) = corrugationOldSlope g S y := by
  have hs := corrugationOldSlope_positive g S y hp hn
  have hsq : (corrugationOldSlope g S y)^2 = g y (metricGradient g S y) (metricGradient g S y) :=
    Real.sq_sqrt (hp _ hn).le
  rw [← metricGradient_pair g S y hp,he,map_smul,smul_eq_mul,← hsq]
  field_simp

end
end Yau.Geometry

end OAI
