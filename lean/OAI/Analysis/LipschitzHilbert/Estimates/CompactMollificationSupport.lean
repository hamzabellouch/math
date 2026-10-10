import OAI.Analysis.LipschitzHilbert.Estimates.CompactMollificationL2

namespace OAI

/-! Shrinking compact mollifiers eventually stay inside any prescribed
open neighbourhood of the original compact support. -/
noncomputable section
open MeasureTheory Function Set Filter
open scoped Topology Pointwise
namespace LipschitzHilbert.PacketRepresentation

theorem compactMollification_eventually_supported (f : (ℝ×ℝ) → ℂ)
    (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (K U : Set (ℝ×ℝ)) (hK : IsCompact K) (hfk : support f⊆K)
    (hU : IsOpen U) (hKU : K⊆U) :
    ∀ᶠ n : ℕ in atTop, support (compactMollification (testMollifier n) f hf hc)⊆U := by
  obtain ⟨V,hV,hVU⟩ := compact_open_separated_add_left hK hU hKU
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp hV
  filter_upwards [testMollifier_radius_tendsto.eventually (gt_mem_nhds hdelta)] with n hn
  exact (compactMollification_support _ f hf hc).trans
    ((Set.add_subset_add ((Metric.ball_subset_ball hn.le).trans hball) hfk).trans hVU)

theorem exists_schwartz_approx_compact (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure)
    (K U : Set (ℝ×ℝ)) (hK : IsCompact K) (hfk : support f⊆K)
    (hU : IsOpen U) (hKU : K⊆U) (epsilon : ℝ) (he : 0<epsilon) :
    ∃ g : SchwartzMap (ℝ×ℝ) ℂ, (∀ z, ‖g z‖≤1) ∧ support g⊆U ∧
      ‖g.toLp 2 planeMeasure-hf2.toLp f‖<epsilon := by
  have hlim := compactMollification_Lp_tendsto f hfm hf hc hb hf2
  have hclose := hlim.eventually (Metric.ball_mem_nhds _ he)
  obtain ⟨n,hn,hns⟩ := (hclose.and (compactMollification_eventually_supported f hf hc K U hK hfk hU hKU)).exists
  refine ⟨compactMollification (testMollifier n) f hf hc,compactMollification_unit _ f hf hc hb,hns,?_⟩
  simpa only [dist_eq_norm] using Metric.mem_ball.mp hn

end LipschitzHilbert.PacketRepresentation

end

end OAI
