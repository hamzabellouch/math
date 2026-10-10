import OAI.Geometry.NodalSets.Charts.CorrugationGridFrames
import OAI.Geometry.NodalSets.Elliptic.CorrugationGridNonvanishing

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

lemma corrugationEnvelopePerturbation_smooth (o : Coord) (L : ℝ) (k : ℕ)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ) (amp : ℝ)
    (e : (Fin 4 → Fin (corrugationSubdivision k)) → Coord ≃L[ℝ] Coord)
    (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (corrugationEnvelopePerturbation o L k g S χ amp e) :=
  corrugationGridSum_smooth o L _ χ hχ _ _ _ _

lemma corrugationEnvelopePerturbation_support (o : Coord) {L : ℝ} (hL : 0 < L) (k : ℕ)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ) (amp : ℝ)
    (e : (Fin 4 → Fin (corrugationSubdivision k)) → Coord ≃L[ℝ] Coord)
    (hχ : tsupport χ ⊆ ball (0:Coord) (1/2)) :
    HasCompactSupport (corrugationEnvelopePerturbation o L k g S χ amp e) ∧
    tsupport (corrugationEnvelopePerturbation o L k g S χ amp e) ⊆ interior (Icc o (fun i ↦ o i+L)) :=
  corrugationGridSum_support o hL (corrugationSubdivision_positive k) χ hχ _ _ _ _

theorem corrugationEnvelopePerturbation_small (o : Coord) {L : ℝ} (hL : 0 < L)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S χ : Coord → ℝ) (amp : ℝ)
    {U : Set Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0)
    (hχ : tsupport χ ⊆ ball (0:Coord) (1/2)) (hχb : ∀ z, |χ z| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → Coord ≃L[ℝ] Coord,
      ∀ x, |corrugationEnvelopePerturbation o L k g S χ amp e x| < ε := by
  obtain ⟨m,hm,B,hB,hs⟩ := corrugationOldSlope_compact_bounds g S isCompact_Icc hU hDU hg hS hp hn
  obtain ⟨M,hM,hbound⟩ := corrugationGridSum_uniform_bound amp
  have ht : Tendsto (fun k ↦ B/corrugationFrequency k*M) atTop (𝓝 0) := by
    simpa [corrugationFrequency] using
      (corrugation_power_reciprocal_tendsto B (by norm_num : (8:ℕ) ≠ 0)).mul_const M
  filter_upwards [ht.eventually_lt_const hε] with k hk
  intro e x
  apply lt_of_le_of_lt _ hk
  exact hbound o L (corrugationSubdivision k) hL (corrugationSubdivision_positive k) χ hχ hχb
    (corrugationFrequency k) B (corrugationFrequency_positive k) hB.le _ e
    (fun i ↦ ⟨(corrugationOldSlope_positive g S _
      (hp _ (hDU (corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i)))
      (hn _ (corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i))).le,
      (hs _ (corrugationCubeCenter_mem o hL (corrugationSubdivision_positive k) i)).2⟩) x

end
end Yau.Geometry

end OAI
