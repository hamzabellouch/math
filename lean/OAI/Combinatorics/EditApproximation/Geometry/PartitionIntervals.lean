import OAI.Combinatorics.EditApproximation.Geometry.AlignmentSplitting
import OAI.Combinatorics.EditApproximation.Geometry.StateGeometry

namespace OAI

/-!
# Valid target states from an actual alignment partition

Prefix lengths convert an ordered list partition of a target substring
to valid global endpoint states. Every returned substring is exactly
the corresponding partition piece, even when pieces are empty.
-/

namespace EditApproximation

theorem flatten_take_length_le {α : Type*} (parts : List (List α)) (k : ℕ) :
    (parts.take k).flatten.length ≤ parts.flatten.length := by
  have h := congrArg (fun p : List (List α) => p.flatten.length)
    (List.take_append_drop k parts)
  simp only [List.flatten_append, List.length_append] at h
  omega

theorem flatten_take_succ_length {α : Type*} (parts : List (List α)) (i : Fin parts.length) :
    (parts.take (i.val + 1)).flatten.length =
      (parts.take i.val).flatten.length + parts[i.val].length := by
  rw [List.take_succ_eq_append_getElem i.isLt]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.length_append]

theorem substring_middle {α : Type*} (pre piece suffix : List α) :
    substring ((pre ++ piece) ++ suffix) pre.length (pre.length + piece.length) = piece := by
  unfold substring
  rw [← List.length_append, List.take_append_length, List.drop_append_length]

theorem substring_flatten_piece {α : Type*} (parts : List (List α)) (i : Fin parts.length) :
    substring parts.flatten (parts.take i.val).flatten.length
      (parts.take (i.val + 1)).flatten.length = parts[i.val] := by
  have hparts : parts.flatten =
      ((parts.take i.val).flatten ++ parts[i.val]) ++ (parts.drop (i.val + 1)).flatten := by
    have h := congrArg List.flatten (List.take_append_drop (i.val + 1) parts)
    rw [List.take_succ_eq_append_getElem i.isLt] at h
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil] using h.symm
  rw [flatten_take_succ_length]
  conv_lhs => arg 1; rw [hparts]
  exact substring_middle _ _ _

def partitionInterval {α : Type*} (target : List α) (q : TargetInterval target.length)
    (parts : List (List α)) (hparts : parts.flatten = substring target q.lo q.hi)
    (i : Fin parts.length) : TargetInterval target.length where
  lo := q.lo + (parts.take i.val).flatten.length
  hi := q.lo + (parts.take (i.val + 1)).flatten.length
  ordered := by rw [flatten_take_succ_length]; omega
  valid := by
    have hprefix := flatten_take_length_le parts (i.val + 1)
    have hlength := congrArg List.length hparts
    simp only [substring, List.length_drop, List.length_take, Nat.min_eq_left q.valid] at hlength
    have horder := q.ordered
    have hvalid := q.valid
    omega

theorem substring_inside_shift {α : Type*} (target : List α)
    (q : TargetInterval target.length) (lo hi : ℕ)
    (hhi : hi ≤ q.hi - q.lo) :
    substring target (q.lo + lo) (q.lo + hi) =
      substring (substring target q.lo q.hi) lo hi := by
  unfold substring
  rw [List.take_drop]
  have htake : q.lo + hi ≤ q.hi := by have h := q.ordered; omega
  simp only [List.take_take, Nat.min_eq_left htake, List.drop_drop]

theorem partitionInterval_substring {α : Type*} (target : List α)
    (q : TargetInterval target.length) (parts : List (List α))
    (hparts : parts.flatten = substring target q.lo q.hi) (i : Fin parts.length) :
    substring target (partitionInterval target q parts hparts i).lo
      (partitionInterval target q parts hparts i).hi = parts[i.val] := by
  have hhi : (parts.take (i.val + 1)).flatten.length ≤ q.hi - q.lo := by
    have h := flatten_take_length_le parts (i.val + 1)
    rw [hparts] at h
    simpa only [substring, List.length_drop, List.length_take, Nat.min_eq_left q.valid] using h
  change substring target (q.lo + (parts.take i.val).flatten.length)
    (q.lo + (parts.take (i.val + 1)).flatten.length) = parts[i.val]
  rw [substring_inside_shift target q _ _ hhi, ← hparts]
  exact substring_flatten_piece parts i

theorem partitionInterval_shared {α : Type*} (target : List α)
    (q : TargetInterval target.length) (parts : List (List α))
    (hparts : parts.flatten = substring target q.lo q.hi)
    (i j : Fin parts.length) (hnext : j.val = i.val + 1) :
    (partitionInterval target q parts hparts i).hi =
      (partitionInterval target q parts hparts j).lo := by
  simp only [partitionInterval, hnext]

end EditApproximation

end OAI
