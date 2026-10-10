import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ImageClass

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq B] [DecidableEq U]

abbrev ExchangeIndex (B U : Type*) := U ⊕ (B × U)

noncomputable def classSlots (psi : B → U) (slot : B ↪ U) (u : U) : Finset U :=
  (imageClass psi u).map slot
noncomputable def auxiliarySlots (psi : B → U) (slot : B ↪ U) (u : U) : Finset U :=
  (classSlots psi slot u).erase u
noncomputable def exchangeWeight (psi : B → U) (slot : B ↪ U) : ExchangeIndex B U → ℝ
  | .inl u => if 0 < (imageClass psi u).card ∧ (imageClass psi u).card ≤ 5 then 1 else 0
  | .inr (b,s) => if 5 < (imageClass psi (psi b)).card ∧ s ∈ auxiliarySlots psi slot (psi b)
      then 1 / ((imageClass psi (psi b)).card - (1:ℝ)) else 0
noncomputable def exchangeRemove (psi : B → U) (slot : B ↪ U) : ExchangeIndex B U → Finset U
  | .inl u => classSlots psi slot u
  | .inr (_,s) => {s}
noncomputable def exchangeAdd (psi : B → U) : ExchangeIndex B U → Finset B
  | .inl u => imageClass psi u
  | .inr (b,_) => {b}

omit [Fintype U] [DecidableEq B] in
lemma auxiliary_slot_mem (psi : B → U) (slot : B ↪ U) (b : B) (u : U) :
    slot b ∈ auxiliarySlots psi slot u ↔ psi b = u ∧ slot b ≠ u := by
  simp only [auxiliarySlots,Finset.mem_erase,classSlots,Finset.mem_map]
  constructor
  · rintro ⟨hne,c,hc,he⟩
    have hcb : c = b := slot.injective he
    exact ⟨by simpa only [hcb] using (Finset.mem_filter.mp hc).2,hne⟩
  · rintro ⟨hb,hne⟩
    exact ⟨hne,b,by simp [imageClass,hb],rfl⟩

omit [Fintype U] in
lemma auxiliary_card (psi : B → U) (slot : B ↪ U)
    (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b) (b : B) :
    (auxiliarySlots psi slot (psi b)).card = (imageClass psi (psi b)).card - 1 := by
  rw [auxiliarySlots,classSlots,Finset.card_erase_of_mem (image_mem_class_slots psi slot hslot b)]
  simp

omit [Fintype U] [DecidableEq B] in
lemma imageClass_pos (psi : B → U) (b : B) : 0 < (imageClass psi (psi b)).card := by
  apply Finset.card_pos.mpr
  exact ⟨b,by simp [imageClass]⟩

omit [Fintype U] [DecidableEq B] in
lemma exchangeWeight_nonneg (psi : B → U) (slot : B ↪ U) (e : ExchangeIndex B U) :
    0 ≤ exchangeWeight psi slot e := by
  cases e with
  | inl u => simp only [exchangeWeight]; split_ifs <;> norm_num
  | inr bs =>
    obtain ⟨b,s⟩ := bs
    simp only [exchangeWeight]
    split_ifs with h
    · have ht : (1:ℝ) < ((imageClass psi (psi b)).card:ℝ) := by exact_mod_cast (by omega : 1 < (imageClass psi (psi b)).card)
      positivity
    · rfl

omit [Fintype U] [DecidableEq B] in
lemma exchange_width (psi : B → U) (slot : B ↪ U) (e : ExchangeIndex B U)
    (he : 0 < exchangeWeight psi slot e) :
    (exchangeRemove psi slot e).card = (exchangeAdd psi e).card ∧
    (exchangeAdd psi e).card ≤ 5 := by
  cases e with
  | inl u =>
    simp only [exchangeWeight] at he
    split_ifs at he with h
    · simp [exchangeRemove,exchangeAdd,classSlots,h.2]
    · norm_num at he
  | inr bs => obtain ⟨b,s⟩ := bs; simp [exchangeRemove,exchangeAdd]

omit [Fintype U] [DecidableEq B] in
lemma exchange_preserves_image (psi : B → U) (slot : B ↪ U)
    (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b)
    (e : ExchangeIndex B U) (he : 0 < exchangeWeight psi slot e) (b : B)
    (hb : b ∉ exchangeAdd psi e) : psi b ∉ exchangeRemove psi slot e := by
  cases e with
  | inl u =>
    intro hm
    obtain ⟨c,hc,hcs⟩ := Finset.mem_map.mp hm
    have hp := slot_class_preservation psi slot hslot hcs
    have hcu := (Finset.mem_filter.mp hc).2
    apply hb
    simp [exchangeAdd,imageClass,← hcu,← hp]
  | inr bs =>
    obtain ⟨c,s⟩ := bs
    simp only [exchangeWeight] at he
    split_ifs at he with h
    · intro hm
      have hbs : psi b = s := Finset.mem_singleton.mp hm
      obtain ⟨d,hd,hds⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase h.2)
      have hdp : psi d = psi b := slot_class_preservation psi slot hslot (hds.trans hbs.symm)
      have hdc : psi d = psi c := (Finset.mem_filter.mp hd).2
      exact (Finset.ne_of_mem_erase h.2) (hbs.symm.trans (hdp.symm.trans hdc))
    · norm_num at he

lemma total_addition_weight (psi : B → U) (slot : B ↪ U)
    (hslot : ∀ b, ∃ c, psi c = psi b ∧ slot c = psi b) (b : B) :
    (∑ e : ExchangeIndex B U, if b ∈ exchangeAdd psi e then exchangeWeight psi slot e else 0) = 1 := by
  classical
  rw [Fintype.sum_sum_type]
  have hsmall : (∑ u : U, if b ∈ exchangeAdd psi (.inl u) then
      exchangeWeight psi slot (.inl u) else 0) =
      if (imageClass psi (psi b)).card ≤ 5 then (1:ℝ) else 0 := by
    simp only [exchangeAdd,imageClass,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ,ite_true,exchangeWeight]
    simp only [imageClass_pos psi b,true_and]
    rfl
  have hlarge : (∑ bs : B × U, if b ∈ exchangeAdd psi (.inr bs) then
      exchangeWeight psi slot (.inr bs) else 0) =
      if 5 < (imageClass psi (psi b)).card then (1:ℝ) else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [exchangeAdd,Finset.mem_singleton]
    rw [Finset.sum_eq_single b]
    · simp only [ite_true,exchangeWeight]
      by_cases hb : 5 < (imageClass psi (psi b)).card
      · simp only [hb,true_and,ite_true]
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,
          auxiliary_card psi slot hslot b]
        have hc : 1 ≤ (imageClass psi (psi b)).card := by omega
        rw [Nat.cast_sub hc]
        have ht : ((imageClass psi (psi b)).card:ℝ) - 1 ≠ 0 := by
          have ht : (1:ℝ) < ((imageClass psi (psi b)).card:ℝ) := by exact_mod_cast (by omega : 1 < (imageClass psi (psi b)).card)
          linarith
        simpa only [Nat.cast_one] using mul_one_div_cancel ht
      · simp [hb]
    · intros c _ hcb
      simp [Ne.symm hcb]
    · simp
  rw [hsmall,hlarge]
  by_cases hb : (imageClass psi (psi b)).card ≤ 5 <;> simp [hb,not_lt.mpr,lt_of_not_ge]

end MetricKMedianRecovery.LocalSearch

end OAI
