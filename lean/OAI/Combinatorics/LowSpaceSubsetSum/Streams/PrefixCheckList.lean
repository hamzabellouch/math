import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketProgram

namespace OAI

/-! # A family-independent list of the completed prefix checks

These lists describe the hypothetical full traversal for analysis. The
executable search regenerates one task at a time and stops at its first YES.
-/

namespace LowSpaceSubsetSum.RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

def completedArrays (B : ℕ) : List (Fin n) → MaskRestriction n → List (Array (Entry (Fin n)))
  | order, P =>
    let task := { D with maskRestriction := P }
    let out := (task.collect B).state.user
    if out.keys.overflow then
      match order with
      | [] => []
      | i :: rest => completedArrays B rest (P.force i false) ++
          completedArrays B rest (P.force i true)
    else [out.records]

theorem searchRight_eq_any (B : ℕ) (check : Array (Entry (Fin n)) → Bool)
    (order : List (Fin n)) (P : MaskRestriction n) :
    D.searchRight B check order P = (D.completedArrays B order P).any check := by
  induction order generalizing P with
  | nil =>
    simp only [searchRight, completedArrays]
    split <;> simp
  | cons i order ih =>
    simp only [searchRight, completedArrays]
    split
    · rw [List.any_append, ← ih, ← ih]
      split <;> simp_all
    · simp

theorem mem_completedArrays (B : ℕ) (order : List (Fin n)) (P : MaskRestriction n)
    (a : Array (Entry (Fin n))) (ha : a ∈ D.completedArrays B order P) :
    ∃ Q : MaskRestriction n,
      ({ D with maskRestriction := Q }.collect B).state.user.keys.overflow = false ∧
        a = { D with maskRestriction := Q }.entries B := by
  induction order generalizing P with
  | nil =>
    simp only [completedArrays] at ha
    split at ha
    · simp at ha
    · rename_i hc
      have he : a = ({ D with maskRestriction := P }.collect B).state.user.records := by
        simpa only [List.mem_singleton] using ha
      exact ⟨P, Bool.eq_false_iff.mpr hc, he⟩
  | cons i order ih =>
    simp only [completedArrays] at ha
    split at ha
    · rcases List.mem_append.mp ha with hl | hr
      · exact ih (P.force i false) hl
      · exact ih (P.force i true) hr
    · rename_i hc
      have he : a = ({ D with maskRestriction := P }.collect B).state.user.records := by
        simpa only [List.mem_singleton] using ha
      exact ⟨P, Bool.eq_false_iff.mpr hc, he⟩

end LowSpaceSubsetSum.RepresentationParentData

namespace LowSpaceSubsetSum.RepresentationBucketData

variable {n g : ℕ} (D : RepresentationBucketData n g)

def checkList (B : ℕ) : List (Array (Entry (Fin n)) × Array (Entry (Fin n))) :=
  let left := (D.left.collect B).state.user
  if left.keys.overflow then []
  else if left.records.isEmpty then []
  else (D.right.completedArrays B D.topOrder MaskRestriction.empty).map (left.records, ·)

theorem run_eq_any (B : ℕ) (families : Fin 4 → Array (Finset (Fin g))) :
    D.run B families = (D.checkList B).any (fun p => D.check families p.1 p.2) := by
  unfold run checkList
  dsimp only
  split
  · simp
  split
  · simp
  rw [D.right.searchRight_eq_any, List.any_map]
  rfl

end LowSpaceSubsetSum.RepresentationBucketData

end OAI
