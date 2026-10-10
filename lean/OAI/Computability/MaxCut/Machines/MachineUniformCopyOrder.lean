import Mathlib
import OAI.Computability.MaxCut.Games.GapSemantics

namespace OAI

/-!
An exact ordering bridge for uniform copies.

Largest-remainder output groups copies of each occurrence together. A fixed
whole-word copying machine instead repeats the entire occurrence list. These
lists are permutations, not equal serializations. The permutation preserves
every selected occurrence count and the target's actual `countSatisfied`.
-/

namespace MaxCutGames.MachineUniformCopyOrder

def occurrenceMajor {α : Type*} (C : Nat) (edges : List α) : List α :=
  edges.flatMap (fun edge => List.replicate C edge)

def copyMajor {α : Type*} (C : Nat) (edges : List α) : List α :=
  (List.replicate C edges).flatten

theorem occurrenceMajor_perm_copyMajor {α : Type*} (C : Nat) (edges : List α) :
    (occurrenceMajor C edges).Perm (copyMajor C edges) := by
  induction C with
  | zero => simp [occurrenceMajor, copyMajor]
  | succ C ih =>
    have split : (edges ++ occurrenceMajor C edges).Perm
        (occurrenceMajor (C + 1) edges) := by
      simpa only [occurrenceMajor, List.map_id, List.replicate_succ, id_eq] using
        List.map_append_flatMap_perm edges id (fun edge => List.replicate C edge)
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons] using
      split.symm.trans (ih.append_left edges)

theorem selected_count_eq {α : Type*} (C : Nat) (edges : List α)
    (keep : α → Bool) :
    ((occurrenceMajor C edges).filter keep).length =
      ((copyMajor C edges).filter keep).length :=
  ((occurrenceMajor_perm_copyMajor C edges).filter keep).length_eq

theorem mem_iff {α : Type*} (C : Nat) (edges : List α) (edge : α) :
    edge ∈ occurrenceMajor C edges ↔ edge ∈ copyMajor C edges :=
  (occurrenceMajor_perm_copyMajor C edges).mem_iff

theorem copyMajor_selected_count {α : Type*} (C : Nat) (edges : List α)
    (keep : α → Bool) :
    ((copyMajor C edges).filter keep).length = C * (edges.filter keep).length := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    change (((edges ++ copyMajor C edges).filter keep).length) = _
    rw [List.filter_append, List.length_append, ih]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem occurrenceMajor_selected_count {α : Type*} (C : Nat) (edges : List α)
    (keep : α → Bool) :
    ((occurrenceMajor C edges).filter keep).length = C * (edges.filter keep).length := by
  rw [selected_count_eq, copyMajor_selected_count]

/-- Encoded rows retain their multiplicities; this does not identify concatenated
bitstreams in two different occurrence orders. -/
theorem encoded_rows_perm {α β : Type*} (C : Nat) (edges : List α)
    (encode : α → List β) :
    ((occurrenceMajor C edges).map encode).Perm ((copyMajor C edges).map encode) :=
  (occurrenceMajor_perm_copyMajor C edges).map encode

open MaxCutGames.Foundations.Target

/-- The actual finite-target satisfaction counter is unaffected by the reorder. -/
theorem countSatisfied_eq {n q : Nat} (C : Nat)
    (edges : List (Constraint n q)) (labeling : Fin n → Fin q) :
    countSatisfied labeling (occurrenceMajor C edges) =
      countSatisfied labeling (copyMajor C edges) :=
  MaxCutGames.Integration.InstanceEquivalences.countSatisfied_perm labeling
    (occurrenceMajor_perm_copyMajor C edges)

end MaxCutGames.MachineUniformCopyOrder

end OAI
