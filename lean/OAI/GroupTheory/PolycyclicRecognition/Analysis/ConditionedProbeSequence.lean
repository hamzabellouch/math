import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConditionedProbeSelection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Shrinking profile tolerances without losing probe volume -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The tolerance tends to zero by a slow diagonal choice. The starting
profile event may have very small mass; the retained independent probe
set still has measure greater than one quarter. -/
theorem eventually_exists_compact_conditioned_probes
    {X Y : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, MeasurableSpace (Y n)] [∀ n, TopologicalSpace (Y n)]
    (μ : ∀ n, Measure (X n)) (ν : ∀ n, Measure (Y n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    [∀ n, (ν n).InnerRegular]
    (E : ∀ n, ℕ → Set (X n)) (bad : ∀ n, ℕ → Set (X n × Y n))
    (hE : ∀ n j, MeasurableSet (E n j))
    (hbad : ∀ n j, MeasurableSet (bad n j))
    (hpos : ∀ j, ∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ n in atTop, c ≤ μ n (E n j))
    (hlim : ∀ j, Tendsto (fun n => (μ n).prod (ν n) (bad n j)) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ n in atTop,
      ∃ x ∈ E n (k n), ∃ K : Set (Y n), IsCompact K ∧
        K ⊆ {y | (x, y) ∉ bad n (k n)} ∧ (1 / 4 : ℝ≥0∞) < ν n K := by
  have hsmall (j : ℕ) : ∀ᶠ n in atTop,
      (μ n).prod (ν n) (bad n j) < (1 / 2 : ℝ≥0∞) * μ n (E n j) := by
    obtain ⟨c, hc, he⟩ := hpos j
    have hh : (0 : ℝ≥0∞) < 1 / 2 * c := ENNReal.mul_pos (by norm_num) hc.ne'
    filter_upwards [(hlim j).eventually (gt_mem_nhds hh), he] with n hn hm
    apply hn.trans_le
    simpa only [mul_comm] using (mul_le_mul_right hm (1 / 2))
  obtain ⟨k, hk, hsmallk⟩ := exists_slow_sequence_selection _ hsmall
  refine ⟨k, hk, hsmallk.mono ?_⟩
  intro n hn
  exact exists_start_with_compact_good_probes (μ n) (ν n)
    (E n (k n)) (bad n (k n)) (hE n (k n)) (hbad n (k n)) hn

end PolycyclicRecognition

end

end OAI
