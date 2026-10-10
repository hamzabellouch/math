import Mathlib

namespace OAI

section
namespace ElementaryPositivity
open scoped BigOperators

lemma rational_finite_between (s t:Finset ℚ) (h:∀a∈s,∀b∈t,a < b) :
    ∃x:ℚ,(∀a∈s,a < x) ∧ ∀b∈t,x < b := by
  classical
  by_cases hs:s.Nonempty
  · let a:=s.max' hs
    by_cases ht:t.Nonempty
    · let b:=t.min' ht
      obtain ⟨x,hax,hxb⟩:=exists_between (h a (s.max'_mem hs) b (t.min'_mem ht))
      exact ⟨x,fun c hc=>(s.le_max' c hc).trans_lt hax,fun c hc=>hxb.trans_le (t.min'_le c hc)⟩
    · refine ⟨a+1,fun c hc=>(s.le_max' c hc).trans_lt (lt_add_one a),?_⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp ht]
  · by_cases ht:t.Nonempty
    · let b:=t.min' ht
      refine ⟨b-1,?_,fun c hc=>(sub_one_lt b).trans_le (t.min'_le c hc)⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp hs]
    · exact ⟨0,by simp [Finset.not_nonempty_iff_eq_empty.mp hs],by simp [Finset.not_nonempty_iff_eq_empty.mp ht]⟩

lemma rational_interval_prefix (h:ℕ → ℕ) (hh:Monotone h) (m:ℕ) :
    ∃t:ℕ → ℚ,(∀i  <  m,0 < t i) ∧
      ∀i j,i < j → j < m → t i < t j ∧
        (j≤h i → t j < t i+1) ∧ (h i < j → t i+1 < t j) := by
  classical
  induction m with
  | zero=>exact ⟨fun _=>1,by simp,by omega⟩
  | succ m ih=>
    obtain ⟨t,ht,he⟩:=ih
    let lower:Finset ℚ:={0} ∪ (Finset.range m).image t ∪
      ((Finset.range m).filter (fun i=>h i < m)).image (fun i=>t i+1)
    let upper:Finset ℚ:=((Finset.range m).filter (fun i=>m≤h i)).image (fun i=>t i+1)
    have hcross:∀a∈lower,∀b∈upper,a < b:=by
      intro a ha b hb
      obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hb
      obtain ⟨hjm,hjh⟩:=Finset.mem_filter.mp hj
      have hjm':j < m:=Finset.mem_range.mp hjm
      rcases Finset.mem_union.mp ha with ha|ha
      · rcases Finset.mem_union.mp ha with ha|ha
        · have ha:a=0:=Finset.mem_singleton.mp ha
          rw [ha]
          linarith [ht j hjm']
        · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
          have him:i < m:=Finset.mem_range.mp hi
          rcases lt_trichotomy i j with hij|rfl|hji
          · linarith [(he i j hij hjm').1]
          · exact lt_add_one _
          · exact (he j i hji him).2.1 (le_trans (Nat.le_of_lt him) hjh)
      · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
        obtain ⟨him,hih⟩:=Finset.mem_filter.mp hi
        have hij:i < j:=by
          by_contra hn
          have H:=hh (Nat.le_of_not_gt hn)
          omega
        linarith [(he i j hij hjm').1]
    obtain ⟨x,hxL,hxU⟩:=rational_finite_between lower upper hcross
    have hx0:0 < x:=hxL 0 (by simp [lower])
    have hxt:∀i  <  m,t i < x:=by
      intro i hi
      apply hxL
      simp only [lower,Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩))
    have hxadj:∀i  <  m,m≤h i → x < t i+1:=by
      intro i hi hh
      apply hxU
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hh⟩,rfl⟩
    have hxnon:∀i  <  m,h i < m → t i+1 < x:=by
      intro i hi hh
      apply hxL
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hh⟩,rfl⟩))
    refine ⟨Function.update t m x,?_,?_⟩
    · intro i hi
      by_cases him:i=m
      · simpa [him] using hx0
      · rw [Function.update_of_ne him]
        exact ht i (by omega)
    · intro i j hij hj
      have him:i≠m:=by omega
      rw [Function.update_of_ne him]
      by_cases hjm:j=m
      · subst j
        rw [Function.update_self]
        exact ⟨hxt i hij,hxadj i hij,hxnon i hij⟩
      · rw [Function.update_of_ne hjm]
        exact he i j hij (by omega)
end ElementaryPositivity

end

end OAI
