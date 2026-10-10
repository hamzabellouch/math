import OAI.Analysis.CircleDomains.Sobolev.ScalarEnergyMeasure
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Countably many source points admit shrinking prescribed neighborhoods
whose union has arbitrarily small mass for an atomless finite energy measure. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_shrinking_energy_balls
    (μ : Measure ℂ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (c : ℕ → ℂ) (O : ℕ → Set ℂ) (hO : ∀ n, O n ∈ 𝓝 (c n))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ n, ball (c n) (r n) ⊆ O n) ∧ μ (⋃ n, ball (c n) (r n)) < ε := by
  have hcount : (range c).Countable := countable_range c
  obtain ⟨V, hCV, hV, hμV⟩ := (range c).exists_isOpen_lt_of_lt (μ := μ) ε
    (by rw [hcount.measure_zero μ]; exact hε)
  have hballs (n : ℕ) : ∃ s : ℝ, 0 < s ∧ ball (c n) s ⊆ O n ∩ V :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem (hO n) (hV.mem_nhds (hCV (mem_range_self n))))
  choose s hs hsub using hballs
  let r : ℕ → ℝ := fun n => min (s n) ((n : ℝ)+1)⁻¹
  refine ⟨r, (fun n => lt_min (hs n) (by positivity)), ?_, ?_, ?_⟩
  · apply squeeze_zero (fun n => (le_min (hs n).le (by positivity)))
      (fun n => min_le_right _ _) ?_
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · intro n
    exact (ball_subset_ball (min_le_left _ _)).trans ((hsub n).trans inter_subset_left)
  · apply (measure_mono (iUnion_subset (fun n => ?_))).trans_lt hμV
    exact (ball_subset_ball (min_le_left _ _)).trans ((hsub n).trans inter_subset_right)

end CircleDomainRigidity

end

end OAI
