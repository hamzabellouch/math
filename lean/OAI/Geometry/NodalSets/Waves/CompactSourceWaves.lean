import OAI.Geometry.NodalSets.Charts.AdmissibleChartPatch
import OAI.Geometry.NodalSets.Charts.CompactFrameCover
import OAI.Geometry.NodalSets.Elliptic.UniformTripleBounds
import OAI.Geometry.NodalSets.Waves.TripleSourceWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

abbrev SourceCompactFrameCover (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S : Coord → ℝ) (K : Set Coord) :=
  CompactFrameCover (fun t : K ↦ g t) (fun t : K ↦ sourceHessian g S t)
    (fun t : K ↦ metricGradient g S t)

def coverSourceCenter {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {S : Coord → ℝ} {K : Set Coord} (d : SourceCompactFrameCover g S K)
    (t : d.Parameter) : Coord := (d.center t).val

lemma continuous_coverSourceCenter {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ}
    {S : Coord → ℝ} {K : Set Coord} (d : SourceCompactFrameCover g S K) :
    Continuous (coverSourceCenter d) := continuous_subtype_val.comp d.continuous_center

theorem construct_compact_source_waves
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    {D U : Set Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hwpos : ∀ x ∈ U, 0 < w x) (hp0 : ∀ x ∈ D, metricGradient g S x ≠ 0)
    (hdir : ∀ x ∈ D, ∃ v : Coord,
      g x (metricGradient g S x) v = 0 ∧ g x v v = 1 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x)+
        (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x v v)
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ d : SourceCompactFrameCover g S D,
      Nonempty (TripleSourceWaveData g w S (coverSourceCenter d) d.triple m J K k0) ∧
      ∃ cs > 0, ∃ ce > 0, ∃ Ce > 0, ∀ t : d.Parameter,
        (∀ v, g (coverSourceCenter d t) (metricGradient g S (coverSourceCenter d t)) v = 0 →
          cs*‖v‖^2 ≤ transverseEnergy (g (coverSourceCenter d t)) (d.triple.q t) v) ∧
        ∀ j, ce ≤ sourceDirectionEta (g (coverSourceCenter d t)) (sourceHessian g S (coverSourceCenter d t))
          (metricGradient g S (coverSourceCenter d t)) (d.triple.q t j) ∧
          sourceDirectionEta (g (coverSourceCenter d t)) (sourceHessian g S (coverSourceCenter d t))
            (metricGradient g S (coverSourceCenter d t)) (d.triple.q t j) ≤ Ce := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hp := metricGradient_continuous g hg hpos S hS
  have hH := sourceHessian_continuous g hg hpos S hS
  obtain ⟨d⟩ := exists_compact_frame_cover
    (fun t : D ↦ g t) (fun t : D ↦ sourceHessian g S t)
    (hg.continuous.comp continuous_subtype_val) (hH.comp continuous_subtype_val)
    (fun t ↦ hs t) (fun t ↦ hpos t) (fun t : D ↦ metricGradient g S t)
    (hp.comp continuous_subtype_val) (fun t ↦ hp0 t t.property) (fun t ↦ hdir t t.property)
  have hy := continuous_coverSourceCenter d
  have hn (t : d.Parameter) : metricGradient g S (coverSourceCenter d t) ≠ 0 :=
    hp0 _ (d.center t).property
  have hwd := construct_triple_source_waves g hg hs hpos w hw S hS
    (coverSourceCenter d) hy hn d.triple hU (fun t ↦ hDU (d.center t).property) hwpos m J K k0 hm hJ
  obtain ⟨cs,hcs,hspan⟩ := uniform_transverse_spanning
    (g ∘ coverSourceCenter d) (hg.continuous.comp hy) (fun t ↦ hpos _)
    (metricGradient g S ∘ coverSourceCenter d) (hp.comp hy) hn
    d.triple.q d.triple.continuous_q d.triple.independent d.triple.perpendicular
  obtain ⟨ce,hce,Ce,hCe,heta⟩ := uniform_direction_strictness
    (g ∘ coverSourceCenter d) (sourceHessian g S ∘ coverSourceCenter d)
    (hg.continuous.comp hy) (hH.comp hy) (fun t ↦ hpos _)
    (metricGradient g S ∘ coverSourceCenter d) (hp.comp hy) hn d.triple
  exact ⟨d,hwd,cs,hcs,ce,hce,Ce,hCe,fun t ↦ ⟨hspan t,heta t⟩⟩

end
end Yau.Geometry

end OAI
