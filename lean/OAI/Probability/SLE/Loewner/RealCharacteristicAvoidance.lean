import OAI.Probability.SLE.Geometry.StableTraceAvoidance

namespace OAI

/-! Both signs of a noncolliding real characteristic give stable trace
avoidance. A continuous real characteristic cannot change sides of the
driver without colliding with it. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma StableTraceAvoidance.of_mirror
    {V : ℝ≥0 → ℝ} {T : ℝ≥0} {z : ℂ}
    (h : StableTraceAvoidance (fun t => -V t) T (loewnerMirror z)) :
    StableTraceAvoidance V T z := by
  obtain ⟨r,δ,hr,hδ,hh⟩ := h
  refine ⟨r,δ,hr,hδ,?_⟩
  intro U hU γ G F hw hUV t ht hb
  have hneg : ∀ s ∈ Icc 0 T, |-U s-(-V s)| ≤ δ := by
    intro s hs
    simpa only [neg_sub_neg,abs_sub_comm] using hUV s hs
  apply hh (fun t => -U t) hU.neg (loewnerMirror ∘ γ)
    (fun t z => loewnerMirror (G t (loewnerMirror z)))
    (fun t z => loewnerMirror (F t (loewnerMirror z))) hw.mirror
    hneg t ht
  simpa only [Function.comp_apply,mem_ball,loewnerMirror_dist] using hb

lemma real_characteristic_one_side
    (V : ℝ≥0 → ℝ) (hV : Continuous V) (T : ℝ≥0) (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc 0 (T : ℝ)))
    (hn : ∀ t ∈ Icc 0 (T : ℝ), q t-V t.toNNReal ≠ 0)
    (h0 : 0 < q 0-V 0) :
    ∀ t ∈ Icc 0 (T : ℝ), 0 < q t-V t.toNNReal := by
  intro t ht
  by_contra hh
  have hc : ContinuousOn (fun s => -(q s-V s.toNNReal)) (Icc 0 (T : ℝ)) :=
    (hq.sub (hV.comp continuous_real_toNNReal).continuousOn).neg
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc ht.1
    (hc.mono (Icc_subset_Icc le_rfl ht.2))
    (show (0 : ℝ) ∈ Icc (-(q 0-V (Real.toNNReal 0))) (-(q t-V t.toNNReal)) by
      simp only [Real.toNNReal_zero]
      exact ⟨by linarith,by linarith⟩)
  exact hn s ⟨hs.1,hs.2.trans ht.2⟩ (neg_eq_zero.mp he)

theorem stableTraceAvoidance_of_real_characteristic
    (V : ℝ≥0 → ℝ) (hV : Continuous V) (T : ℝ≥0) (q : ℝ → ℝ)
    (hqd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt q
      (2/(q t-V t.toNNReal)) (Icc 0 (T : ℝ)) t)
    (hn : ∀ t ∈ Icc 0 (T : ℝ), q t-V t.toNNReal ≠ 0) :
    StableTraceAvoidance V T (q 0 : ℂ) := by
  have hq : ContinuousOn q (Icc 0 (T : ℝ)) :=
    fun t ht => (hqd t ht).continuousWithinAt
  have h0 : q 0-V 0 ≠ 0 := by simpa only [Real.toNNReal_zero] using hn 0 ⟨le_rfl,T.coe_nonneg⟩
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have hnd (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : HasDerivWithinAt
        (fun s => -q s) (2/(-q t-(-V t.toNNReal))) (Icc 0 (T : ℝ)) t := by
      rw [show -q t-(-V t.toNNReal)=-(q t-V t.toNNReal) by ring,div_neg]
      exact (hqd t ht).neg
    have hnn (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : -q t-(-V t.toNNReal) ≠ 0 := by
      rw [show -q t-(-V t.toNNReal)=-(q t-V t.toNNReal) by ring]
      exact neg_ne_zero.mpr (hn t ht)
    have hside := real_characteristic_one_side (fun t => -V t) hV.neg T
      (fun s => -q s) hq.neg hnn (by linarith)
    have hc : ContinuousOn (fun s => -q s-(-V s.toNNReal)) (Icc 0 (T : ℝ)) :=
      hq.neg.sub ((hV.comp continuous_real_toNNReal).neg.continuousOn)
    obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr T.coe_nonneg) hc
    have hp := stableTraceAvoidance_of_real_trajectory (fun t => -V t) T (fun s => -q s)
      (hside s hs) hmin hnd
    apply StableTraceAvoidance.of_mirror
    simpa only [loewnerMirror_apply,Complex.conj_ofReal,Complex.ofReal_neg] using hp
  · have hside := real_characteristic_one_side V hV T q hq hn hpos
    have hc : ContinuousOn (fun s => q s-V s.toNNReal) (Icc 0 (T : ℝ)) :=
      hq.sub (hV.comp continuous_real_toNNReal).continuousOn
    obtain ⟨s,hs,hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr T.coe_nonneg) hc
    exact stableTraceAvoidance_of_real_trajectory V T q (hside s hs) hmin hqd

end SLEExactGauge

end

end OAI
