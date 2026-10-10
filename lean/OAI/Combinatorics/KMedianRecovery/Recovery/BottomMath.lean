import Mathlib

namespace OAI

namespace MetricKMedianRecovery.Completion
lemma separated_sum_le {α : Type*} [DecidableEq α] (v : α→ℝ) (S Y : Finset α)
    (hc : S.card=Y.card) (h : ∀ s∈S,∀ y∈Y,y∉S→v s≤v y) :
    ∑ s∈S,v s≤∑ y∈Y,v y := by
  have hd : (S\Y).card=(Y\S).card := by
    rw [Finset.card_sdiff,Finset.card_sdiff,Finset.inter_comm Y S,hc]
  by_cases hn : (S\Y).Nonempty
  · obtain ⟨m,hm,hmax⟩:=(S\Y).exists_max_image v hn
    have hl := Finset.sum_le_sum (s:=S\Y) (fun s hs=>hmax s hs)
    have hr := Finset.sum_le_sum (s:=Y\S) (fun y hy=>h m (Finset.mem_sdiff.mp hm).1 y
      (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2)
    simp only [Finset.sum_const,nsmul_eq_mul] at hl hr
    have hs := Finset.sum_inter_add_sum_sdiff S Y v
    have hy := Finset.sum_inter_add_sum_sdiff Y S v
    rw [Finset.inter_comm Y S] at hy
    rw [hd] at hl
    linarith
  · have hz : S\Y=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
    have hsub : S⊆Y:=Finset.sdiff_eq_empty_iff_subset.mp hz
    exact (congrArg (fun U : Finset α=>∑ u∈U,v u) (Finset.eq_of_subset_of_card_le hsub hc.ge)).le

variable {α : Type*} [LinearOrder α]
def bottomSet (U : Finset α) (k : ℕ) : Finset α := ((U.sort (·≤·)).take k).toFinset
lemma bottomSet_subset (U : Finset α) (k : ℕ) : bottomSet U k⊆U := by
  intro x hx
  exact (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))
lemma bottomSet_card (U : Finset α) (k : ℕ) : (bottomSet U k).card=min k U.card := by
  rw [bottomSet,List.toFinset_card_of_nodup ((U.sort_nodup (·≤·)).sublist (List.take_sublist _ _)),List.length_take,Finset.length_sort]
lemma bottomSet_separated (U : Finset α) (k : ℕ) (x : α) (hx : x∈bottomSet U k)
    (y : α) (hy : y∈U) (hn : y∉bottomSet U k) : x<y := by
  have hp := (Finset.sortedLT_sort U).pairwise
  have hpair : ((U.sort (·≤·)).take k++(U.sort (·≤·)).drop k).Pairwise (·<·) := by
    rw [List.take_append_drop]
    exact hp
  have hy' : y∈(U.sort (·≤·)).drop k := by
    have hm := (Finset.mem_sort (·≤·)).mpr hy
    rw [←List.take_append_drop k (U.sort (·≤·)),List.mem_append] at hm
    exact hm.resolve_left (fun h=>hn (List.mem_toFinset.mpr h))
  exact (List.pairwise_append.mp hpair).2.2 x (List.mem_toFinset.mp hx) y hy'
lemma bottomSet_sum_le (v : α→ℝ) (hv : Monotone v) (U : Finset α) (k : ℕ)
    (Y : Finset α) (hY : Y⊆U) (hc : Y.card=min k U.card) :
    ∑ x∈bottomSet U k,v x≤∑ y∈Y,v y := by
  apply separated_sum_le v _ Y ((bottomSet_card U k).trans hc.symm)
  intro x hx y hy hn
  exact hv (le_of_lt (bottomSet_separated U k x hx y (hY hy) hn))
end MetricKMedianRecovery.Completion

end OAI
