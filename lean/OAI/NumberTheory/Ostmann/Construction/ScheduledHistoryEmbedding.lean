import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyBounds
import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveFrequencySupport

namespace OAI

/-! # Embedding the actual varying-cutoff histories without adding bottom frequencies -/

namespace Ostmann
open scoped BigOperators Classical

def frequencyTreeInFinset (S : Finset ℤ) : (n : ℕ) → (t : FrequencyTree ℤ n) →
    (∀ s ∈ allFrequencyList n t, s ∈ S) → FrequencyTree S n
  | 0, t, h => ⟨t, h t (by simp [allFrequencyList])⟩
  | n + 1, t, h =>
    (⟨t.1, h t.1 (List.mem_cons_self ..)⟩,
      frequencyTreeInFinset S n t.2.1
        (fun s hs => h s (List.mem_cons_of_mem _ (List.mem_append_left _ hs))),
      frequencyTreeInFinset S n t.2.2
        (fun s hs => h s (List.mem_cons_of_mem _ (List.mem_append_right _ hs))))

theorem frequencyTreeInFinset_map (S : Finset ℤ) (n : ℕ) (t : FrequencyTree ℤ n)
    (h : ∀ s ∈ allFrequencyList n t, s ∈ S) :
    frequencyTreeMap Subtype.val n (frequencyTreeInFinset S n t h) = t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases t with ⟨s, l, r⟩
    change (s, frequencyTreeMap Subtype.val n (frequencyTreeInFinset S n l _),
      frequencyTreeMap Subtype.val n (frequencyTreeInFinset S n r _)) = (s, l, r)
    exact congrArg₂ (fun l r => (s, l, r)) (ih _ _) (ih _ _)

abbrev NonzeroScheduledHistory (V : ℕ → ℕ) (n : ℕ) :=
  {a : ScheduledFrequencyIndex V n //
    ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0}

noncomputable instance nonzeroScheduledHistoryFintype (V : ℕ → ℕ) (n : ℕ) :
    Fintype (NonzeroScheduledHistory V n) := by
  infer_instance

noncomputable def scheduledHistoryEmbedding (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ) :
    NonzeroScheduledHistory V n ↪ FrequencyTree ((transferFrequencyRange (V n)).erase 0) n where
  toFun a := frequencyTreeInFinset _ n (scheduledFrequencyHistory V n a.val) (by
    intro s hs
    exact Finset.mem_erase.mpr ⟨a.property s hs,
      (mem_transferFrequencyRange _ _).mpr (scheduledFrequencyHistory_all_bound V hV n a.val s hs)⟩)
  inj' := by
    intro a b h
    apply Subtype.ext
    apply scheduledFrequencyHistory_injective V n
    have hh := congrArg (frequencyTreeMap Subtype.val n) h
    simpa only [frequencyTreeInFinset_map] using hh

theorem scheduledHistoryEmbedding_map (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n) :
    frequencyTreeMap Subtype.val n (scheduledHistoryEmbedding V hV n a) =
      scheduledFrequencyHistory V n a.val :=
  frequencyTreeInFinset_map _ _ _ _

theorem scheduledFrequencyHistory_leaf_cutoff (V : ℕ → ℕ) (n : ℕ)
    (a : ScheduledFrequencyIndex V n) :
    frequencyLeafWeight (fun v : ℤ => if v.natAbs ≤ V 0 then (1 : ℝ) else 0)
      n (scheduledFrequencyHistory V n a) = 1 := by
  induction n with
  | zero =>
    exact ite_eq_left (scheduledFrequencyHistory_root_bound V 0 a)
  | succ n ih =>
    change frequencyLeafWeight _ n (scheduledFrequencyHistory V n a.2.1) *
      frequencyLeafWeight _ n (scheduledFrequencyHistory V n a.2.2) = 1
    rw [ih, ih, mul_one]

theorem scheduledHistoryEmbedding_leaf_cutoff (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : NonzeroScheduledHistory V n) :
    frequencyLeafWeight (singleFrequencyLeaf ((transferFrequencyRange (V n)).erase 0) (V 0))
      n (scheduledHistoryEmbedding V hV n a) = 1 := by
  have h := scheduledFrequencyHistory_leaf_cutoff V n a.val
  rw [← scheduledHistoryEmbedding_map V hV n a, frequencyLeafWeight_map] at h
  exact h

/-- Only internal frequencies are enlarged to the largest cutoff. Zero
frequencies contribute nothing, and every bottom frequency keeps cutoff V 0. -/
theorem scheduled_history_sum_le (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (F : FrequencyTree ℤ n → ℝ) (hF : ∀ t, 0 ≤ F t)
    (hzero : ∀ a : ScheduledFrequencyIndex V n,
      ¬(∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0) →
        F (scheduledFrequencyHistory V n a) = 0) :
    (∑ a, F (scheduledFrequencyHistory V n a)) ≤
      ∑ t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n,
        if frequencyLeafWeight (singleFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
          (V 0)) n t = 1 then F (frequencyTreeMap Subtype.val n t) else 0 := by
  let p := fun a : ScheduledFrequencyIndex V n =>
    ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0
  have hz : (∑ a : {a // ¬p a}, F (scheduledFrequencyHistory V n a.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hzero a.val a.property
  have hs := Fintype.sum_subtype_add_sum_subtype p
    (fun a => F (scheduledFrequencyHistory V n a))
  rw [hz, add_zero] at hs
  rw [← hs]
  let e := scheduledHistoryEmbedding V hV n
  let G := fun t : FrequencyTree ((transferFrequencyRange (V n)).erase 0) n =>
    if frequencyLeafWeight (singleFrequencyLeaf ((transferFrequencyRange (V n)).erase 0)
      (V 0)) n t = 1 then F (frequencyTreeMap Subtype.val n t) else 0
  have he (a : NonzeroScheduledHistory V n) : G (e a) = F (scheduledFrequencyHistory V n a.val) := by
    dsimp only [G, e]
    rw [scheduledHistoryEmbedding_leaf_cutoff, ite_eq_left rfl, scheduledHistoryEmbedding_map]
  change (∑ a : NonzeroScheduledHistory V n, F (scheduledFrequencyHistory V n a.val)) ≤ ∑ t, G t
  simp_rw [← he]
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
    intro t _ _
    dsimp only [G]
    split_ifs
    · exact hF _
    · exact le_rfl)

end Ostmann

end OAI
