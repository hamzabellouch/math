import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.IndexedWitnessCode
import OAI.Combinatorics.TriangleRemoval.Queries.Address
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixCodeSet

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.PathForest
variable {s : ℕ} {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma address_head (F : PathForest s) (key : Fin s → α) (i : Fin s) :
    (F.address key i).head? = some (key i) := by
  cases hp : F.parent i with
  | none => rw [F.address_none key i hp]; rfl
  | some j => rw [F.address_some key i j hp]; rfl

omit [DecidableEq α] in
lemma address_injective (F : PathForest s) {key : Fin s → α}
    (hk : Function.Injective key) : Function.Injective (F.address key) := by
  intro i j h
  apply hk
  exact Option.some.inj (by simpa only [F.address_head] using congrArg List.head? h)

lemma prefix_address_mem (F : PathForest s) (key : Fin s → α) (i : Fin s) (p : List α) :
    p ∈ prefixCodeSet (F.address key i).reverse ↔
      ∃ j, F.Ancestor j i ∧ p = (F.address key j).reverse := by
  induction i using (measure (fun i : Fin s => i.val)).wf.induction with
  | h i ih =>
    cases hp : F.parent i with
    | none =>
      rw [F.address_none key i hp]
      simp only [List.reverse_singleton,prefixCodeSet,Finset.image_empty,Finset.mem_insert,
        Finset.notMem_empty,or_false]
      constructor
      · intro h
        exact ⟨i,Relation.ReflTransGen.refl,by rw [F.address_none key i hp]; exact h⟩
      · rintro ⟨j,hj,rfl⟩
        rcases F.ancestor_eq_or_predecessor hj with he | ⟨k,hk,_⟩
        · subst j
          rw [F.address_none key i hp]; rfl
        · exact False.elim (by change F.parent i = some k at hk; rw [hp] at hk; cases hk)
    | some k =>
      have hi : (F.address key i).reverse = (F.address key k).reverse ++ [key i] := by
        rw [F.address_some key i k hp,List.reverse_cons]
      rw [hi,prefixCodeSet_append_singleton,Finset.mem_insert,ih k (F.property i k hp)]
      constructor
      · rintro (h | ⟨j,hj,h⟩)
        · exact ⟨i,Relation.ReflTransGen.refl,h.trans hi.symm⟩
        · exact ⟨j,hj.tail hp,h⟩
      · rintro ⟨j,hj,rfl⟩
        rcases F.ancestor_eq_or_predecessor hj with rfl | ⟨l,hl,hjl⟩
        · exact Or.inl hi
        · have he := F.predecessor_unique hl hp
          subst l
          exact Or.inr ⟨j,hjl,rfl⟩

lemma prefix_option_address_mem (F : PathForest s) (key : Fin s → α)
    (a : Option (Fin s)) (p : List α) :
    p ∈ prefixCodeSet (a.elim [] (F.address key)).reverse ↔
      ∃ j, F.OnPath a j ∧ p = (F.address key j).reverse := by
  cases a with
  | none => simp [prefixCodeSet,OnPath]
  | some i =>
    simp only [Option.elim_some,F.prefix_address_mem,OnPath,Option.some.injEq]
    constructor
    · rintro ⟨j,hj,hp⟩
      exact ⟨j,⟨i,rfl,hj⟩,hp⟩
    · rintro ⟨j,⟨i',rfl,hj⟩,hp⟩
      exact ⟨j,hj,hp⟩

lemma two_mark_exact_size (F : PathForest s) {key : Fin s → α}
    (hk : Function.Injective key) (a b : Option (Fin s))
    (hcover : ∀ i, F.OnPath a i ∨ F.OnPath b i) :
    let p := (a.elim [] (F.address key)).reverse
    let q := (b.elim [] (F.address key)).reverse
    (splitQueryPaths p q).1.length + (splitQueryPaths p q).2.1.length +
      (splitQueryPaths p q).2.2.length = s := by
  dsimp only
  rw [← prefixCodeSet_union_card]
  have he : prefixCodeSet (a.elim [] (F.address key)).reverse ∪
      prefixCodeSet (b.elim [] (F.address key)).reverse =
        Finset.univ.image (fun i => (F.address key i).reverse) := by
    ext p
    simp only [Finset.mem_union,F.prefix_option_address_mem,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro (⟨j,_,rfl⟩ | ⟨j,_,rfl⟩) <;> exact ⟨j,rfl⟩
    · rintro ⟨j,rfl⟩
      rcases hcover j with h | h
      · exact Or.inl ⟨j,h,rfl⟩
      · exact Or.inr ⟨j,h,rfl⟩
  rw [he,Finset.card_image_of_injective]
  · exact Finset.card_fin s
  · exact List.reverse_injective.comp (F.address_injective hk)

end SharpTerminalLeave.PathForest

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

noncomputable instance indexedWitnessCodeAddressFintype {K s : ℕ} (E : Graph K) (birth : Fin s → Fin K)
    (mark : Fin K → Option (Fin s)) : Fintype (IndexedWitnessCode E birth mark) := by
  classical
  unfold IndexedWitnessCode
  infer_instance

end SharpTerminalLeave

end

end OAI
