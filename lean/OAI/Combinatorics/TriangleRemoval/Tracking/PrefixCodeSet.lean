import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.SplitQueryPaths

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def prefixCodeSet {A : Type*} [DecidableEq A] : List A → Finset (List A)
  | [] => ∅
  | a::p => insert [a] ((prefixCodeSet p).image (List.cons a))

lemma nil_not_mem_prefixCodeSet {A : Type*} [DecidableEq A] (p : List A) :
    [] ∉ prefixCodeSet p := by
  cases p with
  | nil => simp [prefixCodeSet]
  | cons a p => simp [prefixCodeSet]

lemma prefixCodeSet_card {A : Type*} [DecidableEq A] (p : List A) :
    (prefixCodeSet p).card = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [prefixCodeSet,Finset.card_insert_of_notMem,Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),ih,List.length_cons]
    intro h
    obtain ⟨q,hq,h⟩ := Finset.mem_image.mp h
    have he : q = [] := List.cons.inj h |>.2
    subst q
    exact nil_not_mem_prefixCodeSet p hq

lemma prefixCodeSet_cons_disjoint {A : Type*} [DecidableEq A] {a b : A}
    (hab : a ≠ b) (p q : List A) :
    Disjoint (prefixCodeSet (a::p)) (prefixCodeSet (b::q)) := by
  apply Finset.disjoint_left.mpr
  intro l hl hr
  have hhead {x : A} {t : List A} (h : l ∈ prefixCodeSet (x::t)) : l.head? = some x := by
    rw [prefixCodeSet] at h
    rcases Finset.mem_insert.mp h with rfl | h
    · rfl
    · obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp h
      rfl
  exact hab (Option.some.inj ((hhead hl).symm.trans (hhead hr)))

lemma prefixCodeSet_union_card {A : Type*} [DecidableEq A] (p q : List A) :
    (prefixCodeSet p ∪ prefixCodeSet q).card =
      (splitQueryPaths p q).1.length + (splitQueryPaths p q).2.1.length +
        (splitQueryPaths p q).2.2.length := by
  induction p generalizing q with
  | nil => simp [prefixCodeSet,splitQueryPaths,prefixCodeSet_card]
  | cons a p ih =>
    cases q with
    | nil => simpa only [prefixCodeSet,Finset.union_empty,splitQueryPaths,List.length_nil,zero_add,Nat.add_zero] using prefixCodeSet_card (a::p)
    | cons b q =>
      by_cases hab : a = b
      · subst b
        have he : prefixCodeSet (a::p) ∪ prefixCodeSet (a::q) =
            insert [a] ((prefixCodeSet p ∪ prefixCodeSet q).image (List.cons a)) := by
          simp only [prefixCodeSet,Finset.image_union,Finset.insert_union,Finset.union_insert,Finset.insert_idem]
        rw [he,Finset.card_insert_of_notMem,Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),ih]
        · simp only [splitQueryPaths,↓reduceIte,List.length_cons]
          omega
        · intro h
          obtain ⟨t,ht,ht0⟩ := Finset.mem_image.mp h
          have he : t = [] := List.cons.inj ht0 |>.2
          subst t
          rcases Finset.mem_union.mp ht with h | h
          · exact nil_not_mem_prefixCodeSet p h
          · exact nil_not_mem_prefixCodeSet q h
      · rw [Finset.card_union_of_disjoint (prefixCodeSet_cons_disjoint hab p q),
          prefixCodeSet_card,prefixCodeSet_card]
        simp only [splitQueryPaths,hab,↓reduceIte,List.length_nil,zero_add]

lemma prefixCodeSet_append_singleton {A : Type*} [DecidableEq A] (p : List A) (a : A) :
    prefixCodeSet (p++[a]) = insert (p++[a]) (prefixCodeSet p) := by
  induction p with
  | nil => simp [prefixCodeSet]
  | cons b p ih =>
    simp only [List.cons_append,prefixCodeSet,ih,Finset.image_insert]
    exact Finset.insert_comm _ _ _

end SharpTerminalLeave

end

end OAI
