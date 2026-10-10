import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringAddresses
import OAI.Computability.VertexCover.PCP.PoweringTest

namespace OAI

                                                                                              

namespace UniqueGames.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

private theorem match_in_tail (p : X → Prop) {a : X} {xs : List X}
    (h : ∃ b ∈ a :: xs, p b) (ha : ¬p a) : ∃ b ∈ xs, p b := by
  obtain ⟨b, hb, hp⟩ := h
  rcases List.mem_cons.mp hb with he | hm
  · exact False.elim (ha (he ▸ hp))
  · exact ⟨b, hm, hp⟩

def firstIndex (p : X → Prop) [DecidablePred p] :
    (xs : List X) → (∃ a ∈ xs, p a) → Fin xs.length
  | [], h => False.elim (by simp at h)
  | a :: xs, h =>
    if ha : p a then ⟨0, Nat.zero_lt_succ xs.length⟩ else
      (firstIndex p xs (match_in_tail p h ha)).succ

theorem get_firstIndex (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a),
      xs.get (firstIndex p xs h) = (scanWitness p xs h).val := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h
    by_cases ha : p a
    · simp [firstIndex, scanWitness, ha]
    · simpa only [firstIndex, scanWitness, ha, dite_false, List.get_cons_succ'] using
        ih (match_in_tail p h ha)

theorem firstIndex_matches (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) : p (xs.get (firstIndex p xs h)) := by
  rw [get_firstIndex]
  exact (scanWitness p xs h).property

theorem firstIndex_is_first (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a) (j : Fin xs.length),
      j.val < (firstIndex p xs h).val → ¬p (xs.get j) := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h j
    by_cases ha : p a
    · simp [firstIndex, ha]
    · refine Fin.cases (by intro _; exact ha) (fun i => ?_) j
      intro hi
      apply ih (match_in_tail p h ha) i
      exact Nat.lt_of_succ_lt_succ (by
        simpa only [firstIndex, ha, dite_false, Fin.val_succ] using hi)

abbrev AddressIndex (d t : Nat) := Fin (allAddresses d t).length

variable {vertices d : Nat}

def addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) : AddressIndex d t :=
  firstIndex (fun w => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

theorem addressIndex_get (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (allAddresses d t).get (addressIndex G t center u) =
      (finitePortSelector G t center).address u := by
  change (allAddresses d t).get (firstIndex
    (fun w => (wordToBall G t center w).val = u.val) (allAddresses d t) _) =
      (scanWitness _ _ _).val
  exact get_firstIndex _ _ _

theorem addressIndex_matches (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    wordToBall G t center ((allAddresses d t).get (addressIndex G t center u)) = u := by
  rw [addressIndex_get]
  exact (finitePortSelector G t center).correct u

theorem addressIndex_is_first (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (j : AddressIndex d t)
    (hj : j.val < (addressIndex G t center u).val) :
    (wordToBall G t center ((allAddresses d t).get j)).val ≠ u.val := by
  exact firstIndex_is_first _ _ _ j hj

theorem addressIndex_lt (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (addressIndex G t center u).val < ∑ n : Fin (t + 1), d ^ n.val := by
  rw [← length_allAddresses]
  exact (addressIndex G t center u).isLt

abbrev LabelTable (d t : Nat) (A : Type*) := Vector A (allAddresses d t).length

def labelTable {t : Nat} (a : PaddedLabel (Fin d) t A) : LabelTable d t A :=
  Vector.ofFn fun i => a ((allAddresses d t).get i)

@[simp] theorem labelTable_get {t : Nat} (a : PaddedLabel (Fin d) t A)
    (i : AddressIndex d t) :
    (labelTable a)[i] = a ((allAddresses d t).get i) := by
  simp [labelTable]

theorem labelTable_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (a : PaddedLabel (Fin d) t A) :
    (labelTable a)[addressIndex G t center u] =
      decode (finitePortSelector G t center) a u := by
  rw [labelTable_get, addressIndex_get]
  rfl

structure WalkOpinionRow (vertices d t : Nat) where
  edge : Edge (Fin vertices) (Fin d)
  tailIndex : AddressIndex d t
  headIndex : AddressIndex d t

abbrev WalkRows (vertices d n : Nat) := Vector (WalkOpinionRow vertices d (n + 1)) (n + 1)

def walkRows (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : WalkRows vertices d n :=
  Vector.ofFn fun k =>
    { edge := edgeAt G n w k
      tailIndex := addressIndex G (n + 1) w.1 (tailFromStart G n w k)
      headIndex := addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) }

@[simp] theorem walkRows_edge (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    (walkRows G n w)[k].edge = edgeAt G n w k := by
  simp [walkRows]

@[simp] theorem walkRows_tail_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable a)[(walkRows G n w)[k].tailIndex] =
      decode (finitePortSelector G (n + 1) w.1) a (tailFromStart G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) w.1 (tailFromStart G n w k) a

@[simp] theorem walkRows_head_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (b : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable b)[(walkRows G n w)[k].headIndex] =
      decode (finitePortSelector G (n + 1) (endpoint G w)) b (headFromEnd G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) b

theorem walkRows_length (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) :
    (walkRows G n w).toList.length = n + 1 := by
  simp

def rowsAccepts {n : Nat} (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool)
    (rows : WalkRows vertices d n) (a b : LabelTable d (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1), accepts rows[k].edge a[rows[k].tailIndex]
    b[rows[k].headIndex] = true)

theorem rowsAccepts_walkRows (G : PortGraph (Fin vertices) (Fin d))
    (accepts : Edge (Fin vertices) (Fin d) → A → A → Bool) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (a b : PaddedLabel (Fin d) (n + 1) A) :
    rowsAccepts accepts (walkRows G n w) (labelTable a) (labelTable b) =
      PoweringTest.pathAccepts G accepts n (finitePortSelector G (n + 1)) w a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowsAccepts, decide_eq_true_iff, PoweringTest.pathAccepts_eq_true_iff,
    walkRows_edge, walkRows_tail_value, walkRows_head_value]

end UniqueGames.Foundations.PCP.PoweringOpinionTables

end OAI
