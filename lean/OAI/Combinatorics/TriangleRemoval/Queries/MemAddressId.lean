import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Queries.RecordedCallForest
import OAI.Combinatorics.TriangleRemoval.Process.EdgeMatching
import OAI.Combinatorics.TriangleRemoval.Process.PathForest
import OAI.Combinatorics.TriangleRemoval.Queries.Address

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
variable {s : ℕ} {α : Type*}

lemma mem_address_id (F : PathForest s) (i j : Fin s) :
    i ∈ F.address id j ↔ F.Ancestor i j := by
  induction j using (measure (fun j : Fin s => j.val)).wf.induction with
  | h j ih =>
    cases hp : F.parent j with
    | none =>
      rw [F.address_none id j hp,List.mem_singleton]
      constructor
      · rintro rfl
        exact Relation.ReflTransGen.refl
      · intro h
        rcases F.ancestor_eq_or_predecessor h with he | ⟨k,hk,_⟩
        · exact he
        · exact False.elim (by change F.parent j = some k at hk; rw [hp] at hk; cases hk)
    | some k =>
      rw [F.address_some id j k hp,List.mem_cons,ih k (F.property j k hp)]
      constructor
      · rintro (rfl | hik)
        · exact Relation.ReflTransGen.refl
        · exact hik.tail hp
      · intro h
        rcases F.ancestor_eq_or_predecessor h with he | ⟨l,hl,hil⟩
        · exact Or.inl he
        · have he := F.predecessor_unique hl hp
          subst l
          exact Or.inr hil

lemma address_map (F : PathForest s) (key : Fin s → α) (i : Fin s) :
    F.address key i = (F.address id i).map key := by
  induction i using (measure (fun i : Fin s => i.val)).wf.induction with
  | h i ih =>
    cases hp : F.parent i with
    | none => rw [F.address_none key i hp,F.address_none id i hp]; rfl
    | some j =>
      rw [F.address_some key i j hp,F.address_some id i j hp,
        ih j (F.property i j hp)]
      rfl

lemma option_address_length (F : PathForest s) (key : Fin s → α) (a : Option (Fin s)) :
    (a.elim [] (F.address key)).length = (a.elim [] (F.address id)).length := by
  cases a with
  | none => rfl
  | some i => simp only [Option.elim_some,F.address_map key,List.length_map]

lemma mem_option_address (F : PathForest s) (a : Option (Fin s)) (i : Fin s) :
    i ∈ a.elim [] (F.address id) ↔ F.OnPath a i := by
  cases a with
  | none => simp [OnPath]
  | some j =>
    simp only [Option.elim_some,F.mem_address_id,OnPath,Option.some.injEq]
    exact ⟨fun h => ⟨j,rfl,h⟩,fun ⟨w,hw,h⟩ => hw ▸ h⟩

lemma two_mark_size (F : PathForest s) (key : Fin s → α) (a b : Option (Fin s))
    (hcover : ∀ i, F.OnPath a i ∨ F.OnPath b i) :
    s ≤ (a.elim [] (F.address key)).length + (b.elim [] (F.address key)).length := by
  classical
  rw [F.option_address_length key a,F.option_address_length key b]
  have hsub : (Finset.univ : Finset (Fin s)) ⊆
      (a.elim [] (F.address id)).toFinset ∪ (b.elim [] (F.address id)).toFinset := by
    intro i _
    rcases hcover i with h | h
    · exact Finset.mem_union_left _ (List.mem_toFinset.mpr ((F.mem_option_address a i).mpr h))
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr ((F.mem_option_address b i).mpr h))
  calc
    s = (Finset.univ : Finset (Fin s)).card := (Finset.card_fin s).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)

end SharpTerminalLeave.PathForest

open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
