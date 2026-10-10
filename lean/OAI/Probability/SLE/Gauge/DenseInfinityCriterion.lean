import Mathlib

namespace OAI

/-! A countable test for a continuous function's limit at infinity on an
open planar domain. Only the values on one fixed dense sequence are used. -/
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology

namespace SLEExactGauge

def DenseInfinityCriterion (f : ℂ → ℂ) (D : Set ℂ) (c : ℂ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ,
    (N:ℝ) < ‖denseSeq ℂ n‖ → denseSeq ℂ n ∈ D →
      ‖f (denseSeq ℂ n)-c‖ ≤ 1/((k:ℝ)+1)

lemma denseInfinityCriterion_of_tendsto {f : ℂ → ℂ} {D : Set ℂ} {c : ℂ}
    (h : Tendsto f (cocompact ℂ ⊓ 𝓟 D) (𝓝 c)) : DenseInfinityCriterion f D c := by
  intro k
  have he := (Metric.tendsto_nhds.mp h) (1/((k:ℝ)+1)) (by positivity)
  rw [eventually_inf_principal,← Metric.cobounded_eq_cocompact] at he
  obtain ⟨R,_,hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  obtain ⟨N,hN⟩ := exists_nat_gt R
  refine ⟨N,fun n hn hD => ?_⟩
  simpa only [dist_eq_norm] using (hR ((hN.trans hn).le) hD).le

lemma DenseInfinityCriterion.bound {f : ℂ → ℂ} {D : Set ℂ} {c : ℂ}
    (hD : IsOpen D) (hf : ContinuousOn f D) (h : DenseInfinityCriterion f D c)
    (k : ℕ) : ∃ N : ℕ, ∀ z ∈ D, (N:ℝ)<‖z‖ → ‖f z-c‖ ≤ 1/((k:ℝ)+1) := by
  obtain ⟨N,hN⟩ := h k
  refine ⟨N,fun z hz hNz => ?_⟩
  by_contra hn
  have hbad : 1/((k:ℝ)+1)<‖f z-c‖ := lt_of_not_ge hn
  have hc : ContinuousAt (fun w => ‖f w-c‖) z :=
    (((hf z hz).continuousAt (hD.mem_nhds hz)).sub_const c).norm
  have hb : {w : ℂ | 1/((k:ℝ)+1)<‖f w-c‖} ∈ 𝓝 z :=
    hc.preimage_mem_nhds (Ioi_mem_nhds hbad)
  have hr : {w : ℂ | (N:ℝ)<‖w‖} ∈ 𝓝 z :=
    continuous_norm.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hNz)
  obtain ⟨n,hnD,hnR,hnB⟩ := (denseRange_denseSeq ℂ).mem_nhds
    (inter_mem (hD.mem_nhds hz) (inter_mem hr hb))
  exact (not_lt_of_ge (hN n hnR hnD)) hnB

lemma DenseInfinityCriterion.tendsto {f : ℂ → ℂ} {D : Set ℂ} {c : ℂ}
    (hD : IsOpen D) (hf : ContinuousOn f D) (h : DenseInfinityCriterion f D c) :
    Tendsto f (cocompact ℂ ⊓ 𝓟 D) (𝓝 c) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)).exists
  obtain ⟨N,hN⟩ := h.bound hD hf k
  rw [eventually_inf_principal]
  have hn : ∀ᶠ z : ℂ in cocompact ℂ, (N:ℝ)<‖z‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop (N:ℝ))
  filter_upwards [hn] with z hz hDz
  simpa only [dist_eq_norm] using (hN z hDz hz).trans_lt hk

end SLEExactGauge

end

end OAI
