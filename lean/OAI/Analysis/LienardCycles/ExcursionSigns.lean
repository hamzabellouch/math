import OAI.Analysis.LienardCycles.ExcursionGraph

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
namespace QuinticLienard
lemma HasDerivAt.pos_right_of_pos {f : ℝ → ℝ} {s d : ℝ}
    (hd : HasDerivAt f d s) (h0 : f s=0) (hpos : 0<d) : ∀ᶠ t in 𝓝[>] s,0<f t := by
  have hl := hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE s)
  filter_upwards [hl.eventually (eventually_gt_nhds hpos),self_mem_nhdsWithin] with t ht hst
  rw [slope_def_field,h0,sub_zero] at ht
  exact (div_pos_iff.mp ht).resolve_right (fun h=> (not_lt_of_ge (sub_nonneg.mpr hst.le)) h.2) |>.1
lemma HasDerivAt.nonneg_of_pos_right {f : ℝ → ℝ} {s t d : ℝ}
    (hd : HasDerivAt f d s) (h0 : f s=0) (hst : s<t) (hf : ∀ v ∈ Ioo s t,0<f v) : 0≤d := by
  apply ge_of_tendsto (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE s))
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hst).filter_mono inf_le_left] with v hsv hvt
  rw [slope_def_field,h0,sub_zero]
  exact (div_pos (hf v ⟨hsv,hvt⟩) (sub_pos.mpr hsv)).le
lemma HasDerivAt.nonpos_of_pos_left {f : ℝ → ℝ} {s t d : ℝ}
    (hd : HasDerivAt f d t) (h0 : f t=0) (hst : s<t) (hf : ∀ v ∈ Ioo s t,0<f v) : d≤0 := by
  apply le_of_tendsto (hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t))
  filter_upwards [self_mem_nhdsWithin,(eventually_gt_nhds hst).filter_mono inf_le_left] with v hvt hsv
  rw [slope_def_field,h0,sub_zero]
  exact (div_neg_of_pos_of_neg (hf v ⟨hsv,hvt⟩) (sub_neg.mpr hvt)).le
lemma IsRightExcursion.endpoint_signs {F : Polynomial ℝ} {z : ℝ → Plane} {s t : ℝ}
    (hz : IsSolution F z) (hn : ∃ s t,z s≠z t) (he : IsRightExcursion z s t) :
    (z t).2<F.eval 0 ∧ F.eval 0<(z s).2 := by
  have hs := HasDerivAt.nonneg_of_pos_right (hz.x_deriv s) he.left he.lt he.positive
  have ht := HasDerivAt.nonpos_of_pos_left (hz.x_deriv t) he.right he.lt he.positive
  rw [he.left] at hs
  rw [he.right] at ht
  exact ⟨lt_of_le_of_ne (sub_nonpos.mp ht) (hz.axis_transverse hn he.right),
    lt_of_le_of_ne (sub_nonneg.mp hs) (hz.axis_transverse hn he.left).symm⟩
lemma IsSolution.right_excursion_after {F : Polynomial ℝ} {z : ℝ → Plane}
    (hz : IsSolution F z) (hn : ∃ u v,z u≠z v) {T : ℝ} (hT : 0<T)
    (hp : Function.Periodic z T) {s : ℝ} (hs : (z s).1=0) (hy : F.eval 0<(z s).2) :
    ∃ t,IsRightExcursion z s t := by
  let S : Set ℝ := {t ∈ Ioc s (s+T) | (z t).1=0}
  have hS : S.Finite := (hz.axis_finite hn s (s+T)).subset (fun _ h=>⟨⟨h.1.1.le,h.1.2⟩,h.2⟩)
  have hne : S.Nonempty := ⟨s+T,⟨by constructor <;> linarith,hp s ▸ hs⟩⟩
  obtain ⟨t,ht,hmin⟩ := hS.isCompact.exists_isMinOn hne continuous_id.continuousOn
  have hst : s<t := ht.1.1
  refine ⟨t,hst,hs,ht.2,?_⟩
  have hd : 0<(z s).2-F.eval (z s).1 := by rw [hs];exact sub_pos.mpr hy
  have he := HasDerivAt.pos_right_of_pos (hz.x_deriv s) hs hd
  intro v hv
  by_contra! hvn
  have hew : ∀ᶠ w in 𝓝[>] s,s<w ∧ w<v ∧ 0<(z w).1 := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hv.1).filter_mono inf_le_left,he] with w hsw hwv hwp
    exact ⟨hsw,hwv,hwp⟩
  obtain ⟨w,hw,hwv,hwp⟩ := hew.exists
  obtain ⟨q,hq,hqz⟩ := intermediate_value_Icc' hwv.le hz.continuous.fst.continuousOn ⟨hvn,hwp.le⟩
  have hqS : q ∈ S := ⟨⟨hw.trans_le hq.1,hq.2.trans (hv.2.le.trans ht.1.2)⟩,hqz⟩
  have hh : t≤q := hmin hqS
  exact (not_le_of_gt (hq.2.trans_lt hv.2)) hh
end QuinticLienard

end OAI
