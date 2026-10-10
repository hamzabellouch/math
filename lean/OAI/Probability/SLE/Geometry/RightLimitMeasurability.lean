import Mathlib

namespace OAI

/-! A measurable right-limit criterion for a family continuous away from the
endpoint. The interval suprema control all heights, not just a sequence. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace SLEExactGauge

def rightLimitError {Ω : Type*} (f : ℝ → Ω → ℂ) (g : Ω → ℂ)
    (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ y : Ioo (0:ℝ) (1/((n:ℝ)+1)), edist (f y ω) (g ω)

lemma measurable_rightLimitError {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → Ω → ℂ) (g : Ω → ℂ)
    (hf : ∀ y, Measurable (f y)) (hg : Measurable g)
    (hc : ∀ ω, ContinuousOn (fun y => f y ω) (Ioi 0)) (n : ℕ) :
    Measurable (rightLimitError f g n) := by
  suffices Measurable (⨆ y : Ioo (0:ℝ) (1/((n:ℝ)+1)),
      fun ω => edist (f y ω) (g ω)) by
    change Measurable (fun ω => ⨆ y : Ioo (0:ℝ) (1/((n:ℝ)+1)), edist (f y ω) (g ω))
    convert this using 1
    funext ω
    exact (iSup_apply (f := fun y : Ioo (0:ℝ) (1/((n:ℝ)+1)) =>
      fun ω => edist (f y ω) (g ω))).symm
  apply measurable_iSup_of_lowerSemicontinuous
  · intro y
    exact (hf y).edist hg
  · intro ω
    have hcont : Continuous (fun y : Ioo (0:ℝ) (1/((n:ℝ)+1)) => f y ω) :=
      (hc ω).comp_continuous continuous_subtype_val (fun y => y.property.1)
    exact (hcont.edist continuous_const).lowerSemicontinuous

lemma tendsto_right_iff_interval_errors {Ω : Type*}
    (f : ℝ → Ω → ℂ) (g : Ω → ℂ) (ω : Ω) :
    Tendsto (fun y => f y ω) (𝓝[>] 0) (𝓝 (g ω)) ↔
      ∀ k : ℕ, ∃ n : ℕ, rightLimitError f g n ω ≤
        ENNReal.ofReal (1/((k:ℝ)+1)) := by
  constructor
  · intro h k
    have hk : 0 < (1:ℝ)/((k:ℝ)+1) := by positivity
    obtain ⟨δ,hδ,hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp h _ hk
    obtain ⟨n,hn⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hδ)).exists
    refine ⟨n,iSup_le fun y => ?_⟩
    have hy : dist (y:ℝ) 0 < δ := by
      rw [Real.dist_eq,sub_zero,abs_of_pos y.property.1]
      exact y.property.2.trans hn
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hb y.property.1 hy).le
  · intro h
    apply Metric.tendsto_nhdsWithin_nhds.mpr
    intro ε hε
    obtain ⟨k,hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hε)).exists
    obtain ⟨n,hn⟩ := h k
    refine ⟨1/((n:ℝ)+1),by positivity,?_⟩
    intro y hy hyδ
    have hy0 : 0 < y := hy
    have hy' : y < 1/((n:ℝ)+1) := by
      simpa only [Real.dist_eq,sub_zero,abs_of_pos hy0] using hyδ
    have hb : edist (f y ω) (g ω) ≤ ENNReal.ofReal (1/((k:ℝ)+1)) :=
      (le_iSup (fun z : Ioo (0:ℝ) (1/((n:ℝ)+1)) => edist (f z ω) (g ω))
        ⟨y,hy,hy'⟩).trans hn
    have hd : dist (f y ω) (g ω) ≤ 1/((k:ℝ)+1) := by
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (by simpa only [edist_dist] using hb)
    exact hd.trans_lt hk

lemma measurableSet_tendsto_right {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → Ω → ℂ) (g : Ω → ℂ)
    (hf : ∀ y, Measurable (f y)) (hg : Measurable g)
    (hc : ∀ ω, ContinuousOn (fun y => f y ω) (Ioi 0)) :
    MeasurableSet {ω | Tendsto (fun y => f y ω) (𝓝[>] 0) (𝓝 (g ω))} := by
  simp_rw [tendsto_right_iff_interval_errors f g,Set.ofPred_forall,Set.ofPred_exists]
  exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun n =>
    measurableSet_le (measurable_rightLimitError f g hf hg hc n) measurable_const

end SLEExactGauge

end

end OAI
