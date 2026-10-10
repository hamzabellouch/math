import OAI.Computability.PerfectCompleteness.Machines.CanonicalKeyShapeMachineLemmas
import OAI.Computability.PerfectCompleteness.Reduction.ExactPreliminaryTarget

namespace OAI

section

namespace PerfectCompleteness.ExactTargetOnlineEncoding

open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

private theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

variable {branch : Nat → Nat} {n t v m : Nat} [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats
local notation "C" => CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "target" => ExactPreliminaryTarget.construct
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "edge" => ExactPreliminaryTarget.entry
  (t := t) clauses rows repeats hn hbranch hrows δ

def leftKeys (occurrences : List C) := occurrences.map (fun e => CanonicalGame.leftKey F e.1)

def rightKeys (occurrences : List C) := occurrences.map (fun e => CanonicalGame.rightKey F e.1)

theorem left_online (earlier suffix : List C) (e : C) (split : order = earlier ++ e :: suffix) :
    CanonicalOnlineNames.onlineID (leftKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
        (CanonicalGame.leftKey F e.1) = (edge e).left.val := by
  change _ = (BinaryNameSearch.payloads (CanonicalVertexNames.tokens
    (((order).map Sigma.fst).map (CanonicalGame.leftKey F)))).idxOf
      (CanonicalVertexNames.payload (CanonicalGame.leftKey F e.1))
  rw [List.map_map, split, List.map_append, List.map_cons]
  exact CanonicalOnlineNames.onlineID_eq_global _ _ _

theorem right_online (earlier suffix : List C) (e : C) (split : order = earlier ++ e :: suffix) :
    CanonicalOnlineNames.onlineID (rightKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
        (CanonicalGame.rightKey F e.1) = (edge e).right.val := by
  change _ = (BinaryNameSearch.payloads (CanonicalVertexNames.tokens
    (((order).map Sigma.fst).map (CanonicalGame.rightKey F)))).idxOf
      (CanonicalVertexNames.payload (CanonicalGame.rightKey F e.1))
  rw [List.map_map, split, List.map_append, List.map_cons]
  exact CanonicalOnlineNames.onlineID_eq_global _ _ _

def onlineWords (earlier : List C) (e : C) : List Nat :=
  [CanonicalOnlineNames.onlineID
      (leftKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
      (CanonicalGame.leftKey F e.1),
    CanonicalOnlineNames.onlineID
      (rightKeys (t := t) clauses rows repeats hn hbranch hrows δ earlier)
      (CanonicalGame.rightKey F e.1)] ++ Encoding.tableWords (edge e).projection

theorem onlineWords_eq (earlier suffix : List C) (e : C)
    (split : order = earlier ++ e :: suffix) :
    onlineWords (t := t) clauses rows repeats hn hbranch hrows δ earlier e =
      Encoding.edgeWords (edge e) := by
  unfold onlineWords Encoding.edgeWords
  rw [left_online (t := t) clauses rows repeats hn hbranch hrows δ earlier suffix e split,
    right_online (t := t) clauses rows repeats hn hbranch hrows δ earlier suffix e split]

theorem reverse_edge_fields {l r q : Nat} (e : Edge l r q) (tail : List Bool) :
    (encodeWords (Encoding.tableWords e.projection)).reverse ++
      ((encodeWord e.right.val).reverse ++ ((encodeWord e.left.val).reverse ++ tail)) =
      (encodeWords (Encoding.edgeWords e)).reverse ++ tail := by
  simp only [Encoding.edgeWords, encodeWords_append, encodeWords,
    List.append_nil, List.reverse_append, List.append_assoc]

theorem target_gameBits :
    Encoding.gameBits target =
      encodeWords [(order).length, (order).length,
        FinitePreliminaryCompletion.alphabet branch n t δ, (order).length] ++
      (order).flatMap (fun e => encodeWords (Encoding.edgeWords (edge e))) := by
  change encodeWords
    ([(CompletedVisitOrder.rawOrder (t := t) clauses rows repeats hn hbranch hrows δ).length,
      (CompletedVisitOrder.rawOrder (t := t) clauses rows repeats hn hbranch hrows δ).length,
      FinitePreliminaryCompletion.alphabet branch n t δ, ((order).map edge).length] ++
        ((order).map edge).flatMap Encoding.edgeWords) = _
  rw [encodeWords_append, encodeWords_flatMap]
  apply congrArg₂ List.append
  · apply congrArg encodeWords
    simp only [List.length_map]
    simp only [CompletedVisitOrder.rawOrder, List.length_map]
  · simp only [List.flatMap_map]

end
end PerfectCompleteness.ExactTargetOnlineEncoding

end

end OAI
