import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.ExchangeIndex

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {B U : Type*} [Fintype B] [Fintype U] [DecidableEq B] [DecidableEq U]

omit [Fintype U] [DecidableEq B] in
lemma classSlots_mem (psi : B → U) (slot : B ↪ U) (b : B) (u : U) :
    slot b ∈ classSlots psi slot u ↔ psi b = u := by
  simp only [classSlots,Finset.mem_map,imageClass,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨c,hc,he⟩
    simpa only [slot.injective he] using hc
  · intro hb; exact ⟨b,hb,rfl⟩

omit [DecidableEq B] in
lemma removal_weight_at_slot (psi : B → U) (slot : B ↪ U) (b : B) :
    (∑ e : ExchangeIndex B U,
      if slot b ∈ exchangeRemove psi slot e then exchangeWeight psi slot e else 0) =
    (if (imageClass psi (psi b)).card ≤ 5 then (1:ℝ) else 0) +
    (if 5 < (imageClass psi (psi b)).card ∧ slot b ≠ psi b
      then ((imageClass psi (psi b)).card:ℝ)/((imageClass psi (psi b)).card-1) else 0) := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  · simp only [exchangeRemove,classSlots_mem]
    rw [Finset.sum_ite_eq]
    simp [exchangeWeight,imageClass_pos psi b]
  · rw [Fintype.sum_prod_type]
    simp only [exchangeRemove,Finset.mem_singleton]
    simp_rw [Finset.sum_ite_eq,Finset.mem_univ,ite_true,exchangeWeight,auxiliary_slot_mem]
    have he (c : B) :
        (if 5 < (imageClass psi (psi c)).card ∧ psi b = psi c ∧ slot b ≠ psi c
          then 1 / ((imageClass psi (psi c)).card - (1:ℝ)) else 0) =
        (if psi c = psi b then
          (if 5 < (imageClass psi (psi b)).card ∧ slot b ≠ psi b
            then 1/((imageClass psi (psi b)).card-(1:ℝ)) else 0) else 0) := by
      by_cases hc : psi c = psi b
      · simp [hc]
      · simp [hc,Ne.symm hc]
    rw [Finset.sum_congr rfl (fun c _ => he c),← Finset.sum_filter]
    change (∑ _c ∈ imageClass psi (psi b),
      if 5 < (imageClass psi (psi b)).card ∧ slot b ≠ psi b
      then 1/((imageClass psi (psi b)).card-(1:ℝ)) else 0) = _
    rw [Finset.sum_const,nsmul_eq_mul]
    split_ifs <;> simp [div_eq_mul_inv]

omit [DecidableEq B] in
lemma removal_weight_le (psi : B → U) (slot : B ↪ U) (s : U) :
    (∑ e : ExchangeIndex B U,
      if s ∈ exchangeRemove psi slot e then exchangeWeight psi slot e else 0) ≤ (6/5:ℝ) := by
  classical
  by_cases hs : ∃ b, slot b = s
  · obtain ⟨b,rfl⟩ := hs
    rw [removal_weight_at_slot]
    by_cases ht : (imageClass psi (psi b)).card ≤ 5
    · simp only [ht,ite_true,not_lt.mpr ht,false_and,ite_false,add_zero]
      norm_num
    · have ht5 : 5 < (imageClass psi (psi b)).card := lt_of_not_ge ht
      simp only [ht,ite_false,zero_add,ht5,true_and]
      split_ifs
      · have ht6 : (6:ℝ) ≤ (imageClass psi (psi b)).card := by exact_mod_cast ht5
        have hpos : (0:ℝ) < (imageClass psi (psi b)).card-1 := by linarith
        apply (div_le_iff₀ hpos).mpr
        linarith
      · norm_num
  · have hz : (∑ e : ExchangeIndex B U,
        if s ∈ exchangeRemove psi slot e then exchangeWeight psi slot e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      cases e with
      | inl u =>
        have hm : s ∉ classSlots psi slot u := by
          intro hm
          obtain ⟨b,_,hb⟩ := Finset.mem_map.mp hm
          exact hs ⟨b,hb⟩
        simp only [exchangeRemove,hm,ite_false]
      | inr bs =>
        obtain ⟨b,t⟩ := bs
        by_cases hst : s = t
        · subst t
          have hm : s ∉ auxiliarySlots psi slot (psi b) := by
            intro hm
            obtain ⟨c,_,hc⟩ := Finset.mem_map.mp (Finset.mem_of_mem_erase hm)
            exact hs ⟨c,hc⟩
          simp [exchangeRemove,exchangeWeight,hm]
        · simp [exchangeRemove,hst]
    rw [hz]
    norm_num

end MetricKMedianRecovery.LocalSearch

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

noncomputable def connection (S : Finset V) (p : V) : ℝ :=
  if h : S.Nonempty then S.inf' h (dist p) else 0
noncomputable def cost (D S : Finset V) : ℝ := ∑ p ∈ D, connection S p

lemma connection_nonneg (S : Finset V) (p : V) : 0 ≤ connection S p := by
  unfold connection
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => dist_nonneg)
  · rfl
lemma connection_le {S : Finset V} {p s : V} (hs : s ∈ S) : connection S p ≤ dist p s := by
  rw [connection,dite_eq_left ⟨s,hs⟩]
  exact Finset.inf'_le _ hs
lemma cost_nonneg (D S : Finset V) : 0 ≤ cost D S :=
  Finset.sum_nonneg (fun _ _ => connection_nonneg _ _)
lemma connection_mono {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) (p : V) :
    connection T p ≤ connection S p := by
  simp only [connection,dite_eq_left hS,dite_eq_left (hS.mono hST)]
  exact Finset.le_inf' hS _ (fun _ hs => Finset.inf'_le _ (hST hs))
lemma cost_mono (D : Finset V) {S T : Finset V} (hS : S.Nonempty) (hST : S ⊆ T) :
    cost D T ≤ cost D S := Finset.sum_le_sum (fun p _ => connection_mono hS hST p)

noncomputable def nearest (S : Finset V) (hS : S.Nonempty) (p : V) : V :=
  Classical.choose (Finset.exists_min_image S (dist p) hS)
lemma nearest_mem (S : Finset V) (hS : S.Nonempty) (p : V) : nearest S hS p ∈ S :=
  (Classical.choose_spec (Finset.exists_min_image S (dist p) hS)).1
lemma nearest_distance (S : Finset V) (hS : S.Nonempty) (p : V) :
    dist p (nearest S hS p) = connection S p := by
  rw [connection,dite_eq_left hS]
  exact le_antisymm (Finset.le_inf' hS _
    (Classical.choose_spec (Finset.exists_min_image S (dist p) hS)).2)
    (Finset.inf'_le _ (nearest_mem S hS p))

variable [DecidableEq V]

def WidthLocalMin (F D S : Finset V) (w : ℕ) : Prop :=
  ∀ T ⊆ F, T.card = S.card → (S \ T).card ≤ w → (T \ S).card ≤ w → cost D S ≤ cost D T

lemma padded_not_worse (F D S T : Finset V) (hSF : S ⊆ F) (hTF : T ⊆ F)
    (hT : T.Nonempty) (hts : T.card ≤ S.card) :
    ∃ U ⊆ F, U.card = S.card ∧ T ⊆ U ∧ S \ U ⊆ S \ T ∧ U \ S ⊆ T \ S ∧
      cost D U ≤ cost D T := by
  obtain ⟨U,hTU,hU,hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : T ⊆ T ∪ S) hts
    (Finset.card_le_card (Finset.subset_union_right : S ⊆ T ∪ S))
  refine ⟨U,hU.trans (Finset.union_subset hTF hSF),hcard,hTU,?_,?_,cost_mono D hT hTU⟩
  · intro x hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun hxt => (Finset.mem_sdiff.mp hx).2 (hTU hxt)⟩
  · intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxu,hxs⟩
    rcases Finset.mem_union.mp (hU hxu) with hxt | hxs'
    · exact Finset.mem_sdiff.mpr ⟨hxt,hxs⟩
    · exact (hxs hxs').elim

lemma local_min_le_smaller (F D S : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S w) (T : Finset V) (hTF : T ⊆ F)
    (hT : T.Nonempty) (hcard : T.card ≤ S.card)
    (hremove : (S \ T).card ≤ w) (hadd : (T \ S).card ≤ w) : cost D S ≤ cost D T := by
  obtain ⟨U,hUF,hUS,_,hrem,hnew,hcost⟩ := padded_not_worse F D S T hSF hTF hT hcard
  exact (hlocal U hUF hUS ((Finset.card_le_card hrem).trans hremove)
    ((Finset.card_le_card hnew).trans hadd)).trans hcost

omit [PseudoMetricSpace V] in
lemma exchange_card_le (S R A : Finset V) (hRS : R ⊆ S) (hAR : A.card ≤ R.card) :
    ((S \ R) ∪ A).card ≤ S.card := by
  have hh := Finset.card_sdiff_add_card_eq_card hRS
  exact (Finset.card_union_le _ _).trans (by omega)
omit [PseudoMetricSpace V] in
lemma exchange_diff_bounds (S R A : Finset V) :
    S \ ((S \ R) ∪ A) ⊆ R ∧ ((S \ R) ∪ A) \ S ⊆ A := by
  constructor
  · intro x hx
    by_contra hn
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,hn⟩))
  · intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxu,hxs⟩
    rcases Finset.mem_union.mp hxu with hx | hx
    · exact (hxs (Finset.mem_sdiff.mp hx).1).elim
    · exact hx
lemma local_exchange (F D S : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S w) (R A : Finset V)
    (hRS : R ⊆ S) (hAF : A ⊆ F) (hA : A.Nonempty)
    (hcard : A.card ≤ R.card) (hR : R.card ≤ w) (ha : A.card ≤ w) :
    cost D S ≤ cost D ((S \ R) ∪ A) := by
  have hd := exchange_diff_bounds S R A
  exact local_min_le_smaller F D S w hSF hlocal _
    (Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF)
    (hA.mono Finset.subset_union_right) (exchange_card_le S R A hRS hcard)
    ((Finset.card_le_card hd.1).trans hR) ((Finset.card_le_card hd.2).trans ha)

end MetricKMedianRecovery.LocalSearch

end OAI
