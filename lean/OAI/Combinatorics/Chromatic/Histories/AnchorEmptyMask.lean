import Mathlib
import OAI.Combinatorics.Chromatic.Histories.PacketSortedWords

namespace OAI

section
namespace ElementaryPositivity.Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} {A:Type*} [Fintype A] [LinearOrder A]

omit [Fintype A] [LinearOrder A] in
lemma wordCount_multiset (w:Fin n → A) : (wordCount w).toMultiset=(List.ofFn w:Multiset A) := by
  induction n with
  | zero=>simp [wordCount]
  | succ n ih=>
    simp only [wordCount,Fin.sum_univ_succ,map_add,Finsupp.toMultiset_single,one_nsmul,List.ofFn_succ]
    rw [←wordCount,ih]
    rfl

omit [Fintype A] in
lemma empty_ascent_iff (w:Fin n → A) : ascentMask (·<·) w=∅ ↔ Antitone w := by
  cases n with
  | zero=>simp only [Finset.eq_empty_iff_forall_notMem]; exact ⟨fun _ i=>Fin.elim0 i,fun _ t=>Fin.elim0 t⟩
  | succ N=>
    rw [Fin.antitone_iff_succ_le]
    constructor
    · intro h i
      by_contra hn
      let t:Fin ((N+1)-1):=⟨i.val,by omega⟩
      have ht:t∈ascentMask (·<·) w:=by
        apply (mem_ascentMask _ _ _).mpr
        exact lt_of_not_ge hn
      rw [h] at ht
      exact Finset.notMem_empty t ht
    · intro h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have H:=h ⟨t.val,by omega⟩
      exact (not_lt_of_ge H) ((mem_ascentMask _ _ _).mp ht)

omit [Fintype A] in
lemma antitone_word_unique (w v:Fin n → A) (hw:Antitone w) (hv:Antitone v)
    (hc:wordCount w=wordCount v) : w=v := by
  have hm:(List.ofFn w:Multiset A)=(List.ofFn v:Multiset A):=by rw [←wordCount_multiset,←wordCount_multiset,hc]
  have hp:(List.ofFn w).Perm (List.ofFn v):=Quotient.exact hm
  have hl:List.ofFn w=List.ofFn v:=List.Perm.eq_of_pairwise' (r:=fun a b:A=>a≥b)
    (List.pairwise_ofFn.mpr (fun i j hij=>hw hij.le))
    (List.pairwise_ofFn.mpr (fun i j hij=>hv hij.le)) hp
  exact List.ofFn_injective hl

omit [Fintype A] in
lemma exists_antitone_word (μ:A →₀ ℕ) (hμ:μ.degree=n) :
    ∃w:Fin n → A,wordCount w=μ ∧ Antitone w := by
  let l:=μ.toMultiset.sort (·≥·)
  have hl:l.length=n:=by
    rw [Multiset.length_sort,Finsupp.card_toMultiset]
    exact hμ
  have H:∃w:Fin l.length → A,wordCount w=μ ∧ Antitone w:=by
    refine ⟨l.get,?_,?_⟩
    · apply Finsupp.orderIsoMultiset.injective
      change (wordCount l.get).toMultiset=μ.toMultiset
      rw [wordCount_multiset,List.ofFn_get]
      exact Multiset.sort_eq _ _
    · intro i j hij
      rcases lt_or_eq_of_le hij with hit|rfl
      · exact (List.pairwise_iff_get.mp (Multiset.pairwise_sort μ.toMultiset (·≥·))) i j hit
      · exact le_rfl
  exact hl ▸ H

abbrev EmptyAnchor (μ:A →₀ ℕ):={w:AnchorWord (n:=n) μ // ascentMask (·<·) w.val=∅}

def emptyAnchorEquiv (μ:A →₀ ℕ) (hμ:μ.degree=n) : EmptyAnchor (n:=n) μ ≃ PUnit where
  toFun _:=PUnit.unit
  invFun _:=⟨⟨(exists_antitone_word μ hμ).choose,(exists_antitone_word μ hμ).choose_spec.1⟩,
    (empty_ascent_iff _).mpr (exists_antitone_word μ hμ).choose_spec.2⟩
  left_inv w:=by
    apply Subtype.ext
    apply Subtype.ext
    apply antitone_word_unique
    · exact (exists_antitone_word μ hμ).choose_spec.2
    · exact (empty_ascent_iff _).mp w.property
    · exact (exists_antitone_word μ hμ).choose_spec.1.trans w.val.property.symm
  right_inv _:=rfl
end
end ElementaryPositivity.Packets

end

end OAI
