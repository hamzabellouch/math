import OAI.NumberTheory.Ostmann.Arithmetic.PairedScheduledSum
import OAI.NumberTheory.Ostmann.Arithmetic.PatternFrequencyNormSum

namespace OAI

/-! # The original two scheduled frequency sums satisfy the arithmetic budget -/

namespace Ostmann
open scoped Classical BigOperators

theorem paired_scheduled_frequency_budget (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (D K err : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ V n ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (F : FrequencyTree ℤ n → FrequencyTree ℤ n → ℝ)
    (hF : ∀ a b, 0 ≤ F a b)
    (hzeroL : ∀ a : ScheduledFrequencyIndex V n, ∀ t,
      ¬(∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) →
        F (scheduledFrequencyHistory V n a) t = 0)
    (hzeroR : ∀ t, ∀ a : ScheduledFrequencyIndex V n,
      ¬(∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) →
        F t (scheduledFrequencyHistory V n a) = 0)
    (hpoint : ∀ t : FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
      ((transferFrequencyRange (V n)).erase 0)) n,
      F (frequencyTreeMap Subtype.val n
          (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n false t))
        (frequencyTreeMap Subtype.val n
          (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n true t)) ≤
      err + K * (frequencyLeafWeight (pairedFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
        (V 0)) n t * ((frequencySplitList ((transferFrequencyRange (V n)).erase 0) n t).map
          (pairFrequencySupportBound D)).prod)) :
    (∑ a : ScheduledFrequencyIndex V n, ∑ b : ScheduledFrequencyIndex V n,
      F (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b)) ≤
    (Fintype.card (FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
      ((transferFrequencyRange (V n)).erase 0)) n) : ℝ) * err +
      K * ((8 * D ^ 4 * (1 + Real.log (V n)) ^ 3) ^ (2 ^ n - 1) *
        (2 * (V 0 : ℝ)) ^ (2 * 2 ^ n)) := by
  let S := (transferFrequencyRange (V n)).erase 0
  let H := fun t : FrequencyTree (S × S) n =>
    F (frequencyTreeMap Subtype.val n (frequencyPairProjection S n false t))
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n true t))
  have hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V n := by
    intro s hs
    exact ⟨(Finset.mem_erase.mp hs).1, (mem_transferFrequencyRange _ _).mp (Finset.mem_erase.mp hs).2⟩
  have hbudget := paired_frequency_norm_sum_le S n (V n) (V 0) D K err hD hK hS hdiv
    (fun t => (H t : ℂ)) (fun t => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hF _ _)]
      exact hpoint t)
  have hsum0 : 0 ≤ ∑ t : FrequencyTree (S × S) n, H t := Finset.sum_nonneg (fun _ _ => hF _ _)
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg hsum0] at hbudget
  apply (paired_scheduled_history_sum_le V hV n F hF hzeroL hzeroR).trans
  apply le_trans _ hbudget
  apply Finset.sum_le_sum
  intro t _
  split_ifs with hcut
  · exact le_rfl
  · exact hF _ _

end Ostmann

end OAI
