import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationParentComplete
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryCompleted
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorEncodedCheck

namespace OAI

/-! # Actual depth-first right-parent prefix recomputation -/

namespace LowSpaceSubsetSum

namespace MaskRestriction

variable {n : ℕ}

def force (P : MaskRestriction n) (i : Fin n) (side : Bool) : MaskRestriction n :=
  if side then { P with ones := Insert.insert i P.ones }
  else { P with zeros := Insert.insert i P.zeros }

def follow (P : MaskRestriction n) (order : List (Fin n)) (S : Finset (Fin n)) : MaskRestriction n :=
  order.foldl (fun P i => P.force i (decide (i ∈ S))) P

theorem force_compatible (P : MaskRestriction n) (domain S : Finset (Fin n))
    (h : P.Compatible domain S) (i : Fin n) :
    (P.force i (decide (i ∈ S))).Compatible domain S := by
  by_cases hi : i ∈ S
  · simp only [hi, decide_true, force, ↓reduceIte, Compatible]
    refine ⟨?_, h.2⟩
    intro j hj
    obtain ⟨hj, hjD⟩ := Finset.mem_inter.mp hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact h.1 (Finset.mem_inter.mpr ⟨hj, hjD⟩)
  · simp only [hi, decide_false, force, Bool.false_eq_true, ↓reduceIte, Compatible]
    refine ⟨h.1, Finset.disjoint_left.mpr ?_⟩
    intro j hj hjS
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi hjS
    · exact Finset.disjoint_left.mp h.2 hj hjS

end MaskRestriction

namespace RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

/-- Each task regenerates its restricted leaves and streams. An overflowing
full prefix is dropped; a completed array is passed to the actual checker.
The first YES returns immediately. -/
def searchRight (B : ℕ) (check : Array (Entry (Fin n)) → Bool) :
    List (Fin n) → MaskRestriction n → Bool
  | order, P =>
    let task := { D with maskRestriction := P }
    let out := (task.collect B).state.user
    if out.keys.overflow then
      match order with
      | [] => false
      | i :: rest =>
        if searchRight B check rest (P.force i false) then true
        else searchRight B check rest (P.force i true)
    else check out.records

theorem searchRight_sound (B : ℕ) (check : Array (Entry (Fin n)) → Bool)
    (Q : Prop) (hcheck : ∀ P, check ({ D with maskRestriction := P }.entries B) = true → Q)
    (order : List (Fin n)) (P : MaskRestriction n) (hyes : D.searchRight B check order P = true) : Q := by
  induction order generalizing P with
  | nil =>
    simp only [searchRight] at hyes
    split at hyes
    · contradiction
    · exact hcheck P hyes
  | cons i order ih =>
    simp only [searchRight] at hyes
    split at hyes
    · split at hyes
      · rename_i hl
        exact ih _ hl
      · exact ih _ hyes
    · exact hcheck P hyes

/-- A fitting task at the end of a designated mask path suffices. Earlier
completion reaches the checker; earlier YES also returns immediately. -/
theorem searchRight_complete (B : ℕ) (check : Array (Entry (Fin n)) → Bool)
    (domain S : Finset (Fin n))
    (hfind : ∀ P, P.Compatible domain S →
      ({ D with maskRestriction := P }.collect B).state.user.keys.overflow = false →
        check ({ D with maskRestriction := P }.entries B) = true)
    (order : List (Fin n)) (P : MaskRestriction n) (hP : P.Compatible domain S)
    (hfull : ({ D with maskRestriction := P.follow order S }.collect B).state.user.keys.overflow = false) :
    D.searchRight B check order P = true := by
  induction order generalizing P with
  | nil =>
    have hc : ({ D with maskRestriction := P }.collect B).state.user.keys.overflow = false := hfull
    simpa only [searchRight, hc, Bool.false_eq_true, ↓reduceIte, entries] using hfind P hP hc
  | cons i order ih =>
    by_cases ho : ({ D with maskRestriction := P }.collect B).state.user.keys.overflow = true
    · have hnext := ih (P.force i (decide (i ∈ S))) (P.force_compatible domain S hP i) hfull
      cases hb : decide (i ∈ S) with
      | false =>
        simp only [hb] at hnext
        simp only [searchRight, ho, ↓reduceIte, hnext]
      | true =>
        simp only [hb] at hnext
        simp only [searchRight, ho, ↓reduceIte]
        split
        · rfl
        · exact hnext
    · have hc : ({ D with maskRestriction := P }.collect B).state.user.keys.overflow = false :=
        Bool.eq_false_iff.mpr ho
      simpa only [searchRight, hc, Bool.false_eq_true, ↓reduceIte, entries] using hfind P hP hc
/-- No prefix task can introduce a false YES. This applies to every family
outcome and every overflow pattern, rather than just the surviving bucket. -/
theorem searchRight_subset_sum_sound {g : ℕ} (B : ℕ) (C : TopCoordinates n g)
    (families : Fin 4 → Array (Finset (Fin g))) (left : Array (Entry (Fin n)))
    (order : List (Fin n)) (P : MaskRestriction n) (leftDomain : Finset (Fin n))
    (htop : RepresentationUniverse.topDomain D.leaves = C.domain)
    (htl : Disjoint (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.mixerDomain D.leaves))
    (htb : Disjoint (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.backgroundDomain D.leaves))
    (hlb : Disjoint (RepresentationUniverse.mixerDomain D.leaves)
      (RepresentationUniverse.backgroundDomain D.leaves))
    (hshared : leftDomain ∩ RepresentationUniverse.parentDomain D.leaves ⊆ C.domain)
    (hleft : ∀ e ∈ left.toList, Represents D.weights leftDomain C.domain e)
    (hsize : left.size + (D.capacity + 1) ≤ 2 ^ n)
    (hyes : D.searchRight B (fun right => (C.check families
      ((D.input.target : ℤ) - weight (fun i => (D.input.values i : ℤ)) D.signs)
      left.toList right.toList).accepted) order P = true) : Solvable D.input := by
  apply D.searchRight_sound B _ (Solvable D.input) ?_ order P hyes
  intro P hp
  let task := { D with maskRestriction := P }
  apply C.subset_sum_sound D.input D.signs families left.toList (task.entries B).toList
    (leftDomain := leftDomain) (rightDomain := RepresentationUniverse.parentDomain D.leaves)
    (by
      simp only [Array.length_toList]
      exact (Nat.add_le_add_left (task.storage B).1 _).trans hsize)
    hshared hleft ?_ hp
  intro e he
  rw [← htop]
  exact task.entry_represents B htl htb hlb e he

end RepresentationParentData
end LowSpaceSubsetSum

end OAI
