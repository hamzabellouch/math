import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SubConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile107
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

lemma hasDerivWithinAt_Ici_of_tendsto_right_deriv {J d : ℝ → ℝ} {v : ℝ}
    (hc : ContinuousOn J (Ici 0))
    (hd : ∀ t, 0 < t → HasDerivWithinAt J (d t) (Ici t) t)
    (hv : Tendsto d (𝓝[>] 0) (𝓝 v)) : HasDerivWithinAt J v (Ici 0) 0 := by
  have HB (a t b : ℝ) (ha : 0 < a) (hat : a ≤ t)
      (hb : ∀ s ∈ Ico a t, d s ≤ b) : J t ≤ J a+b*(t-a) := by
    apply image_le_of_liminf_slope_right_le_deriv_boundary (f := J)
      (B := fun s => J a+b*(s-a)) (B' := fun _ => b)
      (hc.mono (fun _ hx => ha.le.trans hx.1)) (by simp) (by fun_prop)
      (fun s _ => by simpa using ((((hasDerivAt_id s).sub_const a).const_mul b).const_add (J a)).hasDerivWithinAt (s := Ici s))
      _ ⟨hat,le_rfl⟩
    intro s hs r hr
    exact (hd s (ha.trans_le hs.1)).liminf_right_slope_le ((hb s hs).trans_lt hr)
  have HL (a t b : ℝ) (ha : 0 < a) (hat : a ≤ t)
      (hb : ∀ s ∈ Ico a t, b ≤ d s) : J a+b*(t-a) ≤ J t := by
    have H : -J t ≤ -J a+(-b)*(t-a) := by
      apply image_le_of_liminf_slope_right_le_deriv_boundary (f := fun s => -J s)
        (B := fun s => -J a+(-b)*(s-a)) (B' := fun _ => -b)
        ((hc.neg).mono (fun _ hx => ha.le.trans hx.1)) (by simp) (by fun_prop)
        (fun s _ => by simpa using ((((hasDerivAt_id s).sub_const a).const_mul (-b)).const_add (-J a)).hasDerivWithinAt (s := Ici s))
        _ ⟨hat,le_rfl⟩
      intro s hs r hr
      exact ((hd s (ha.trans_le hs.1)).neg).liminf_right_slope_le ((neg_le_neg (hb s hs)).trans_lt hr)
    linarith
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev := (Metric.tendsto_nhds.mp hv (ε/2) (half_pos hε))
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhdsWithin_iff.mp hev
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) hδ)] with t ht htd
  change 0 < t at ht
  have htδ : t < δ := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htd
  have Hs (s : ℝ) (hs : 0 < s) (hst : s ≤ t) : v-ε/2 ≤ d s ∧ d s ≤ v+ε/2 := by
    have HH := hδb (show s ∈ Metric.ball (0:ℝ) δ ∩ Ioi 0 from
      ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hs] using hst.trans_lt htδ,hs⟩)
    change dist (d s) v < ε/2 at HH
    rw [Real.dist_eq,abs_sub_lt_iff] at HH
    exact ⟨by linarith,by linarith⟩
  have hup : J t ≤ J 0+(v+ε/2)*t := by
    have hj0 := (hc 0 (by simp)).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    change Tendsto J (𝓝[>] 0) (𝓝 (J 0)) at hj0
    have hid : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hh : Tendsto (fun a : ℝ => J a+(v+ε/2)*(t-a)) (𝓝[>] 0) (𝓝 (J 0+(v+ε/2)*t)) := by
      simpa using hj0.add (((tendsto_const_nhds (x := t)).sub hid).const_mul (v+ε/2))
    apply ge_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin,hid.eventually_lt_const ht] with a ha hat
    exact HB a t (v+ε/2) ha hat.le (fun s hs => (Hs s (ha.trans_le hs.1) hs.2.le).2)
  have hlo : J 0+(v-ε/2)*t ≤ J t := by
    have hj0 := (hc 0 (by simp)).mono (Ioi_subset_Ici_self (a := (0:ℝ)))
    change Tendsto J (𝓝[>] 0) (𝓝 (J 0)) at hj0
    have hid : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hh : Tendsto (fun a : ℝ => J a+(v-ε/2)*(t-a)) (𝓝[>] 0) (𝓝 (J 0+(v-ε/2)*t)) := by
      simpa using hj0.add (((tendsto_const_nhds (x := t)).sub hid).const_mul (v-ε/2))
    apply le_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin,hid.eventually_lt_const ht] with a ha hat
    exact HL a t (v-ε/2) ha hat.le (fun s hs => (Hs s (ha.trans_le hs.1) hs.2.le).1)
  rw [Real.dist_eq,slope_def_field,sub_zero,abs_sub_lt_iff]
  constructor
  · have HH := (div_le_iff₀ ht).mpr (show J t-J 0 ≤ (v+ε/2)*t by linarith)
    linarith
  · have HH := (le_div_iff₀ ht).mpr (show (v-ε/2)*t ≤ J t-J 0 by linarith)
    linarith

end
end InlinedFile107

end OAI
