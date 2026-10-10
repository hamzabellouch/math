import OAI.Analysis.LienardCycles.OpenArch

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs
lemma IsOpenArch.axis_endpoints {φ u : ℝ → ℝ} {A B H : ℝ}
    (hu : IsOpenArch φ u A B) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) (hH : 0<H) (hp : φ H ∈ Ioo A B) (hpeak : u (φ H)=H) :
    axisLower φ H=A ∧ axisUpper φ H=B := by
  have he : ∀ᶠ h in 𝓝[>] (0:ℝ),
      A<lower φ h H ∧ lower φ h H<φ H ∧ φ H<upper φ h H ∧ upper φ h H<B ∧
      u (lower φ h H)=h ∧ u (upper φ h H)=h := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hH).filter_mono inf_le_left] with h hh hHt
    obtain ⟨a,b,ha,hb,hab⟩ := hu.subarch hφ hp hpeak hh hHt
    obtain ⟨hl,hr⟩ := canonical_of_positive_arch hab hφ hh hHt
    rw [hl,hr]
    exact ⟨ha,hab.lower_lt_peak,hab.peak_lt_upper,hb,hab.lower,hab.upper⟩
  have hl := lower_axis_tendsto hφ hc hH
  have hr := upper_axis_tendsto hφ hc hH
  have hal : A≤axisLower φ H := ge_of_tendsto hl (he.mono fun _ h=>h.1.le)
  have hlp : axisLower φ H≤φ H := le_of_tendsto hl (he.mono fun _ h=>h.2.1.le)
  have hpr : φ H≤axisUpper φ H := ge_of_tendsto hr (he.mono fun _ h=>h.2.2.1.le)
  have hrb : axisUpper φ H≤B := le_of_tendsto hr (he.mono fun _ h=>h.2.2.2.1.le)
  have hul : u (axisLower φ H)=0 := tendsto_nhds_unique (hu.continuous.continuousAt.tendsto.comp hl)
    ((tendsto_id.mono_left inf_le_left : Tendsto (fun h : ℝ=>h) (𝓝[>] 0) (𝓝 0)).congr'
      (he.mono fun _ h=>h.2.2.2.2.1.symm))
  have hur : u (axisUpper φ H)=0 := tendsto_nhds_unique (hu.continuous.continuousAt.tendsto.comp hr)
    ((tendsto_id.mono_left inf_le_left : Tendsto (fun h : ℝ=>h) (𝓝[>] 0) (𝓝 0)).congr'
      (he.mono fun _ h=>h.2.2.2.2.2.symm))
  constructor
  · apply le_antisymm _ hal
    by_contra! hn
    have hh := hu.positive _ ⟨hn,hlp.trans_lt hp.2⟩
    rw [hul] at hh
    exact lt_irrefl _ hh
  · apply le_antisymm hrb
    by_contra! hn
    have hh := hu.positive _ ⟨hp.1.trans_le hpr,hn⟩
    rw [hur] at hh
    exact lt_irrefl _ hh
end QuinticLienard.ScalarArcs

end OAI
