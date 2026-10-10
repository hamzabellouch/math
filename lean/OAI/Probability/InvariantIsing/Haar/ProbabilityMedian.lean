import Mathlib

namespace OAI

/-! Existence of a median for every real probability law, including laws with atoms. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace InvariantIsing

theorem probability_real_median (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∃ m : ℝ, (1/2:ℝ) ≤ ν.real (Iic m) ∧ (1/2:ℝ) ≤ ν.real (Ici m) := by
  let F := cdf ν
  let S : Set ℝ := {x | (1/2:ℝ) ≤ F x}
  have htop : ∃ x : ℝ, (1/2:ℝ) < F x := by
    have h := (tendsto_cdf_atTop ν).eventually (lt_mem_nhds (by norm_num : (1/2:ℝ) < 1))
    exact h.exists
  have hbot : ∃ x : ℝ, F x < (1/2:ℝ) := by
    have h := (tendsto_cdf_atBot ν).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
    exact h.exists
  obtain ⟨b,hb⟩ := hbot
  have hne : S.Nonempty := by obtain ⟨x,hx⟩ := htop; exact ⟨x,hx.le⟩
  have hbb : BddBelow S := by
    refine ⟨b,?_⟩
    intro x hx
    by_contra h
    have hm := (monotone_cdf ν) (le_of_not_ge h)
    change (1/2:ℝ) ≤ F x at hx
    exact (not_le_of_gt hb) (hx.trans hm)
  let m := sInf S
  have hright (x : ℝ) (hx : m < x) : (1/2:ℝ) ≤ F x := by
    obtain ⟨y,hy,hyx⟩ := exists_lt_of_csInf_lt hne hx
    exact hy.trans ((monotone_cdf ν) hyx.le)
  have hleft (x : ℝ) (hx : x < m) : F x < (1/2:ℝ) := by
    by_contra h
    have hxS : x ∈ S := le_of_not_gt h
    exact (not_le_of_gt hx) (csInf_le hbb hxS)
  have hfm : (1/2:ℝ) ≤ F m := by
    apply ge_of_tendsto ((F.right_continuous m).mono Ioi_subset_Ici_self)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hright x hx
  have hfl : Function.leftLim F m ≤ (1/2:ℝ) := by
    apply le_of_tendsto (F.mono.tendsto_leftLim m)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hleft x hx).le
  refine ⟨m,?_,?_⟩
  · simpa only [F,cdf_eq_real] using hfm
  · have he : ν (Ici m) = ENNReal.ofReal (1-Function.leftLim F m) := by
      rw [← measure_cdf ν]
      exact (cdf ν).measure_Ici (tendsto_cdf_atTop ν) m
    rw [Measure.real,he,ENNReal.toReal_ofReal (by linarith)]
    linarith

theorem measurable_median {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) :
    ∃ m : ℝ, (1/2:ℝ) ≤ μ.real {ω | f ω ≤ m} ∧ (1/2:ℝ) ≤ μ.real {ω | m ≤ f ω} := by
  obtain ⟨m,hm1,hm2⟩ := probability_real_median (μ.map f)
  refine ⟨m,?_,?_⟩
  · rw [map_measureReal_apply hf measurableSet_Iic] at hm1
    exact hm1
  · rw [map_measureReal_apply hf measurableSet_Ici] at hm2
    exact hm2

end InvariantIsing

end

end OAI
