import Mathlib.Data.Finset.Sort
import Mathlib.Order.RelClasses
import OAI.Combinatorics.BalancedRyser.Probability.ExposureInterleaving

namespace OAI

namespace Balanced.ExposureInterleaving

noncomputable section
attribute [local instance] Classical.propDecidable

variable {n m : ℕ} {γ : ℝ}

abbrev beforeStrictTotalOrder (hγ : 0 < γ) :
    IsStrictTotalOrder (Step n m) (Before γ) where
  irrefl := before_irrefl γ
  trans := fun _ _ _ => before_trans hγ
  trichotomous := fun a b hab hba =>
    ((before_trichotomy γ a b).resolve_left hab).resolve_right hba

abbrev scheduleLinearOrder (hγ : 0 < γ) : LinearOrder (Step n m) := by
  letI := beforeStrictTotalOrder (n := n) (m := m) hγ
  exact linearOrderOfSTO (Before γ)

def schedule (hγ : 0 < γ) : Fin (n + m) ≃ Step n m :=
  (@Fintype.orderIsoFinOfCardEq (Step n m) (scheduleLinearOrder hγ)
    inferInstance (n + m) (by simp [Step])).toEquiv

theorem schedule_lt_iff (hγ : 0 < γ) (i j : Fin (n + m)) :
    Before γ (schedule hγ i) (schedule hγ j) ↔ i < j := by
  exact @OrderIso.lt_iff_lt (Fin (n + m)) (Step n m) inferInstance
    (scheduleLinearOrder hγ).toPreorder
    (@Fintype.orderIsoFinOfCardEq (Step n m) (scheduleLinearOrder hγ)
      inferInstance (n + m) (by simp [Step])) i j

theorem schedule_symm_lt_iff (hγ : 0 < γ) (s t : Step n m) :
    (schedule hγ).symm s < (schedule hγ).symm t ↔ Before γ s t := by
  simpa only [Equiv.apply_symm_apply] using
    (schedule_lt_iff hγ ((schedule hγ).symm s) ((schedule hγ).symm t)).symm

theorem schedule_previousD (hγ : 0 < γ) (t : Fin (n + m)) :
    (Finset.univ.filter fun i : Fin n => (schedule hγ).symm (Sum.inl i) < t) =
      previousD γ (schedule hγ t) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, previousD]
  simpa only [Equiv.symm_apply_apply] using
    schedule_symm_lt_iff hγ (Sum.inl i) (schedule hγ t)

theorem schedule_previousC (hγ : 0 < γ) (t : Fin (n + m)) :
    (Finset.univ.filter fun i : Fin m => (schedule hγ).symm (Sum.inr i) < t) =
      previousC γ (schedule hγ t) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, previousC]
  simpa only [Equiv.symm_apply_apply] using
    schedule_symm_lt_iff hγ (Sum.inr i) (schedule hγ t)

theorem previousD_mono_before (hγ : 0 < γ) {s t : Step n m}
    (hst : Before γ s t) : previousD γ s ⊆ previousD γ t := by
  intro i hi
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, before_trans hγ (Finset.mem_filter.mp hi).2 hst⟩

theorem previousC_mono_before (hγ : 0 < γ) {s t : Step n m}
    (hst : Before γ s t) : previousC γ s ⊆ previousC γ t := by
  intro i hi
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, before_trans hγ (Finset.mem_filter.mp hi).2 hst⟩

theorem currentD_mem_previousD {i : Fin n} {t : Step n m}
    (hi : Before γ (Sum.inl i) t) : i ∈ previousD γ t := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

theorem currentC_mem_previousC {i : Fin m} {t : Step n m}
    (hi : Before γ (Sum.inr i) t) : i ∈ previousC γ t := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

theorem remainingD_eq_sub_previousD (γ : ℝ) (s : Step n m) :
    (remainingD γ s).card = n - (previousD γ s).card := by
  have h := previousD_add_remainingD γ s
  omega

theorem remainingC_eq_sub_previousC (γ : ℝ) (s : Step n m) :
    (remainingC γ s).card = m - (previousC γ s).card := by
  have h := previousC_add_remainingC γ s
  omega

theorem deletion_cutoff_remaining (γ η : ℝ) (i : Fin n)
    (hcut : η < parameter γ (Sum.inl i : Step n m)) :
    η * n ≤ ((n - (previousD γ (Sum.inl i : Step n m)).card : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  rw [← remainingD_eq_sub_previousD, remainingD_at_D]
  change η < (i.val + 1 : ℝ) / n at hcut
  have h := (lt_div_iff₀ hn).mp hcut
  simpa only [Nat.cast_add, Nat.cast_one] using h.le

theorem previousC_card_le (γ : ℝ) (s : Step n m) :
    (previousC γ s).card ≤ m := by
  simpa using (previousC γ s).card_le_univ

theorem schedule_previous_mono (hγ : 0 < γ) {i j : Fin (n + m)} (hij : i < j) :
    previousD γ (schedule hγ i) ⊆ previousD γ (schedule hγ j) ∧
      previousC γ (schedule hγ i) ⊆ previousC γ (schedule hγ j) := by
  have hb := (schedule_lt_iff hγ i j).mpr hij
  exact ⟨previousD_mono_before hγ hb, previousC_mono_before hγ hb⟩

def schedulePrefix (hγ : 0 < γ) (t : Fin (n + m)) : Finset (Step n m) :=
  (Finset.univ.filter fun i : Fin (n + m) => i < t).map (schedule hγ).toEmbedding

theorem mem_schedulePrefix (hγ : 0 < γ) (t : Fin (n + m)) (s : Step n m) :
    s ∈ schedulePrefix hγ t ↔ Before γ s (schedule hγ t) := by
  simp only [schedulePrefix, Finset.mem_map_equiv, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simpa only [Equiv.symm_apply_apply] using
    schedule_symm_lt_iff hγ s (schedule hγ t)

theorem schedulePrefix_eq_disjSum (hγ : 0 < γ) (t : Fin (n + m)) :
    schedulePrefix hγ t =
      (previousD γ (schedule hγ t)).disjSum (previousC γ (schedule hγ t)) := by
  ext s
  cases s with
  | inl i => simp [mem_schedulePrefix, previousD]
  | inr i => simp [mem_schedulePrefix, previousC]

theorem schedulePrefix_card (hγ : 0 < γ) (t : Fin (n + m)) :
    (schedulePrefix hγ t).card = t.val := by
  rw [schedulePrefix, Finset.card_map]
  change (Finset.univ.filter fun i : Fin (n + m) => i.val < t.val).card = t.val
  rw [Fin.card_filter_val_lt, Nat.min_eq_right t.isLt.le]

theorem schedule_previous_cards (hγ : 0 < γ) (t : Fin (n + m)) :
    (previousD γ (schedule hγ t)).card +
      (previousC γ (schedule hγ t)).card = t.val := by
  rw [← Finset.card_disjSum, ← schedulePrefix_eq_disjSum, schedulePrefix_card]

theorem schedule_parameter_antitone (hγ : 0 < γ) :
    Antitone (fun t : Fin (n + m) => parameter γ (schedule hγ t)) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · have hb := (before_iff hγ _ _).mp ((schedule_lt_iff hγ i j).mpr hij)
    rcases hb with hb | ⟨hb, _⟩
    · exact hb.le
    · exact hb.symm.le
  · exact le_rfl

end
end Balanced.ExposureInterleaving

end OAI
