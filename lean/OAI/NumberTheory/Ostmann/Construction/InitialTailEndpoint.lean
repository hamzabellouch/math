import OAI.NumberTheory.Ostmann.Construction.AmbientTailGiantEndpoint
import OAI.NumberTheory.Ostmann.Preliminaries.LargeSummandTails
import OAI.NumberTheory.Ostmann.Preliminaries.TailCollisionCutoff

namespace OAI

/-! # The actual endpoint tail in the initial Poisson statistic -/
namespace Ostmann
open Filter
open scoped Classical

theorem EventuallyPrimeSumset.initial_tail_endpoint
    (hsize : PublishedSummandSizeBound) {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite) (N : ℕ) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp ((4 / 100 : ℝ) * L) ≤ Y → Y ≤ Real.exp L →
      ∀ hi : ℕ, (hi : ℝ) = Real.exp Y →
      let E := positiveSummandTail A (summandTailCutoff Y) hi
      a * Real.sqrt (Real.exp Y) / Y ^ 3 ≤ (E.card : ℝ) ∧ E.Nonempty ∧
      (∀ e ∈ E, (e : ℝ) / Real.exp Y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ e ∈ E, ∀ p : Nat.primesLE (tailCollisionCutoff Y),
        (e : ZMod (p : ℕ)) ∈ tailDensityMask A N p) := by
  obtain ⟨a, ha, htail⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (htail.and (eventual_tailCollisionCutoff N))
  have ht : Tendsto (fun L : ℝ => Real.exp ((4 / 100 : ℝ) * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  refine ⟨a, ha, ?_⟩
  filter_upwards [ht.eventually (eventually_ge_atTop Y₀)] with L hL
  intro Y hYlo _hYhi hi hhi E
  obtain ⟨htail, hcut⟩ := hY₀ Y (hL.trans hYlo)
  have ht := htail hi hhi
  have hcount : a * Real.sqrt (Real.exp Y) / Y ^ 3 ≤ (E.card : ℝ) := by
    simpa only [Real.exp_half] using ht.1
  have hpos : 0 < a * Real.sqrt (Real.exp Y) / Y ^ 3 := by
    have hY : 0 < Y := by linarith [hcut.1]
    positivity
  refine ⟨hcount, Finset.card_pos.mp (Nat.cast_pos.mp (hpos.trans_le hcount)), ?_, ?_⟩
  · intro e he
    obtain ⟨he0, hehi⟩ := ht.2.2.1 e he
    rw [hhi] at hehi
    exact ⟨div_nonneg he0 (Real.exp_nonneg _), (div_le_one (Real.exp_pos _)).mpr hehi⟩
  · intro e he p
    have hp := Nat.mem_primesLE.mp p.property
    apply positiveSummandTail_mem_mask A N (summandTailCutoff Y) hi p hp.2.pos _ he
    exact (Nat.add_le_add_left hp.1 N).trans hcut.2.2

end Ostmann

end OAI
