import OAI.NumberTheory.Ostmann.Construction.PairedScheduledHistory

namespace OAI

/-! # Extending both scheduled frequency sums with their bottom cutoffs intact -/

namespace Ostmann
open scoped Classical BigOperators

theorem paired_scheduled_history_sum_le (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (F : FrequencyTree ℤ n → FrequencyTree ℤ n → ℝ)
    (hF : ∀ a b, 0 ≤ F a b)
    (hzeroL : ∀ a : ScheduledFrequencyIndex V n, ∀ t,
      ¬(∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) →
        F (scheduledFrequencyHistory V n a) t = 0)
    (hzeroR : ∀ t, ∀ a : ScheduledFrequencyIndex V n,
      ¬(∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) →
        F t (scheduledFrequencyHistory V n a) = 0) :
    (∑ a : ScheduledFrequencyIndex V n, ∑ b : ScheduledFrequencyIndex V n,
      F (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b)) ≤
    ∑ t : FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
      ((transferFrequencyRange (V n)).erase 0)) n,
      if frequencyLeafWeight (pairedFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
        (V 0)) n t = 1 then
        F (frequencyTreeMap Subtype.val n
            (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n false t))
          (frequencyTreeMap Subtype.val n
            (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n true t))
      else 0 := by
  let p := fun a : ScheduledFrequencyIndex V n =>
    ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0
  have hr (t : FrequencyTree ℤ n) :
      (∑ b : ScheduledFrequencyIndex V n, F t (scheduledFrequencyHistory V n b)) =
        ∑ b : NonzeroScheduledHistory V n, F t (scheduledFrequencyHistory V n b.val) := by
    have h := Fintype.sum_subtype_add_sum_subtype p (fun b => F t (scheduledFrequencyHistory V n b))
    have hz : (∑ b : {b // ¬p b}, F t (scheduledFrequencyHistory V n b.val)) = 0 :=
      Finset.sum_eq_zero (fun b _ => hzeroR t b.val b.property)
    rw [hz, add_zero] at h
    exact h.symm
  have hl :
      (∑ a : ScheduledFrequencyIndex V n, ∑ b : NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b.val)) =
      ∑ a : NonzeroScheduledHistory V n, ∑ b : NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a.val) (scheduledFrequencyHistory V n b.val) := by
    have h := Fintype.sum_subtype_add_sum_subtype p (fun a =>
      ∑ b : NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a) (scheduledFrequencyHistory V n b.val))
    have hz : (∑ a : {a // ¬p a}, ∑ b : NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a.val) (scheduledFrequencyHistory V n b.val)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact Finset.sum_eq_zero (fun b _ => hzeroL a.val _ a.property)
    rw [hz, add_zero] at h
    exact h.symm
  let e := pairedScheduledHistoryEmbedding V hV n
  let G := fun t : FrequencyTree (((transferFrequencyRange (V n)).erase 0) ×
      ((transferFrequencyRange (V n)).erase 0)) n =>
    if frequencyLeafWeight (pairedFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
      (V 0)) n t = 1 then
      F (frequencyTreeMap Subtype.val n
          (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n false t))
        (frequencyTreeMap Subtype.val n
          (frequencyPairProjection ((transferFrequencyRange (V n)).erase 0) n true t))
    else 0
  have he (a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n) :
      G (e a) = F (scheduledFrequencyHistory V n a.1.val) (scheduledFrequencyHistory V n a.2.val) := by
    dsimp only [G, e]
    rw [pairedScheduledHistoryEmbedding_leaf, ite_eq_left rfl,
      pairedScheduledHistoryEmbedding_projection, pairedScheduledHistoryEmbedding_projection]
    rfl
  calc
    _ = ∑ a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n,
        F (scheduledFrequencyHistory V n a.1.val) (scheduledFrequencyHistory V n a.2.val) := by
      simp_rw [hr]
      rw [hl, Fintype.sum_prod_type]
    _ = ∑ a : NonzeroScheduledHistory V n × NonzeroScheduledHistory V n, G (e a) := by
      exact Finset.sum_congr rfl (fun a _ => (he a).symm)
    _ ≤ ∑ t, G t := by
      rw [← Finset.sum_map]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
        intro t _ _
        dsimp only [G]
        split_ifs
        · exact hF _ _
        · exact le_rfl)

end Ostmann

end OAI
