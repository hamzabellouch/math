import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportedProbeSelection

namespace OAI

/-! # Compact good-probe sequences with harmless initial values -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- Extend the eventual Fubini selection to sequences defined at every
scale. Initial exceptional scales use the full compact probability space;
the actual good-probe property is retained eventually. -/
theorem choose_compact_good_probe_sequence
    {X : Type*} [Nonempty X] {Y : ℕ → Type*}
    [∀ n, TopologicalSpace (Y n)] [∀ n, CompactSpace (Y n)]
    [∀ n, T2Space (Y n)] [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
    (ν : ∀ n, ProbabilityMeasure (Y n)) (Good : ∀ n, X → Set (Y n) → Prop)
    (h : ∀ᶠ n in atTop, ∃ x K, IsCompact K ∧ Good n x K ∧
      (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K) :
    ∃ (x : ℕ → X) (K : ∀ n, Set (Y n)),
      (∀ n, IsCompact (K n) ∧ MeasurableSet (K n) ∧
        (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) (K n)) ∧
      ∀ᶠ n in atTop, Good n (x n) (K n) := by
  classical
  let success := fun n => ∃ x K, IsCompact K ∧ Good n x K ∧
    (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K
  have hall (n : ℕ) : ∃ x K, IsCompact K ∧
      (1 / 4 : ℝ≥0∞) < (ν n : Measure (Y n)) K ∧ (success n → Good n x K) := by
    by_cases hn : success n
    · obtain ⟨x, K, hc, hg, hm⟩ := hn
      exact ⟨x, K, hc, hm, fun _ => hg⟩
    · refine ⟨Classical.choice ‹Nonempty X›, univ, isCompact_univ, ?_, ?_⟩
      · simp only [measure_univ]
        norm_num
      · exact fun hs => (hn hs).elim
  choose x K hc hm hg using hall
  refine ⟨x, K, fun n => ⟨hc n, (hc n).measurableSet, hm n⟩, ?_⟩
  filter_upwards [h] with n hn
  exact hg n hn

end PolycyclicRecognition

end

end OAI
