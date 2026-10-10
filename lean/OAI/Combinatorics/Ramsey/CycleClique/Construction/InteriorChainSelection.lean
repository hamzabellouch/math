import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedUniqueness
import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedProfileOperations

namespace OAI

/-! Select both internal vertices of a single amount-two component, and
otherwise all forward internal representatives of that component. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

namespace AssignedAmounts

theorem chain_length {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) (hne : l ≠ []) :
    l.length = w.sum + w.length + 1 := by
  induction h with
  | nil => exact False.elim (hne rfl)
  | singleton => simp
  | @step x y J B w hx hy hJ hJne ht ih =>
    have hh := ih (by simp)
    simp only [List.length_cons, List.length_append, List.sum_cons] at hh ⊢
    omega

theorem amount_two_shape {l : List V} {w : List ℕ} (h : AssignedAmounts Q l w) (hw : w = [2]) :
    ∃ q u v r, l = [q, u, v, r] ∧ q ∈ Q ∧ r ∈ Q ∧ u ∉ Q ∧ v ∉ Q := by
  cases h with
  | nil => simp at hw
  | singleton => simp at hw
  | @step q r J B w hq hr hJ hJne ht =>
    have hh : J.length = 2 ∧ w = [] := List.cons.inj hw
    obtain ⟨hlen, rfl⟩ := hh
    cases ht with
    | singleton hr =>
      obtain ⟨u, v, rfl⟩ := List.length_eq_two.mp hlen
      exact ⟨q, u, v, r, rfl, hq, hr, hJ u (by simp), hJ v (by simp)⟩

end AssignedAmounts

noncomputable def interiorRepresentatives (Q : Finset V) (l : List V) : List V :=
  (chainRepresentatives Q l).tail

noncomputable def selectedChain (Q : Finset V) (l : List V) : List V :=
  if l.length = 4 then (l.drop 1).take 2 else interiorRepresentatives Q l

theorem interiorRepresentatives_sublist (l : List V) :
    (interiorRepresentatives Q l).Sublist l :=
  (List.tail_sublist _).trans (chainRepresentatives_sublist l)

theorem interiorRepresentatives_outside {l : List V}
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∀ x ∈ interiorRepresentatives Q l, x ∉ Q := by
  cases l with
  | nil => simp [interiorRepresentatives, chainRepresentatives]
  | cons prev xs => exact representativesFrom_outside hsteps

theorem interiorRepresentatives_length {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hlast : ∀ v ∈ l.getLast?, v ∈ Q) :
    (interiorRepresentatives Q l).length = w.length := by
  rw [interiorRepresentatives, List.length_tail, chainRepresentatives_length l hlast, h.length_eq]

theorem selectedChain_sublist (l : List V) : (selectedChain Q l).Sublist l := by
  unfold selectedChain
  split_ifs
  · exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
  · exact interiorRepresentatives_sublist l

theorem twice_length_le_sum {w : List ℕ} (h : ∀ a ∈ w, 2 ≤ a) :
    2 * w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.length_cons, Nat.mul_succ, List.sum_cons]
    omega

theorem amount_profile_eq_two_of_length_four {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hl : l.length = 4) (hmin : ∀ a ∈ w, 2 ≤ a) : w = [2] := by
  have hne : l ≠ [] := by intro he; simp [he] at hl
  have hlen := h.chain_length hne
  have hbound := twice_length_le_sum hmin
  have hW : w.length = 1 := by
    by_cases hw : w = []
    · simp only [hw, List.length_nil, List.sum_nil] at hlen
      omega
    · have hp := List.length_pos_iff.mpr hw
      omega
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hW
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons, List.length_nil] at hlen
  have ha : a = 2 := by omega
  simp only [ha]

theorem selectedChain_outside {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hsteps : l.IsChain (fun x y => ¬ (x ∈ Q ∧ y ∈ Q))) :
    ∀ x ∈ selectedChain Q l, x ∉ Q := by
  unfold selectedChain
  split_ifs with hlen
  · obtain ⟨q, u, v, r, rfl, _, _, hu, hv⟩ :=
      h.amount_two_shape (amount_profile_eq_two_of_length_four h hlen hmin)
    simpa using (show ∀ x ∈ [u, v], x ∉ Q by simp [hu, hv])
  · exact interiorRepresentatives_outside hsteps

theorem selectedChain_length_bounds {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hw : w ≠ []) (hmin : ∀ a ∈ w, 2 ≤ a)
    (hlast : ∀ v ∈ l.getLast?, v ∈ Q) :
    (selectedChain Q l).length + (if l.length = 4 then 0 else 1) = w.length + 1 ∧
      w.length + 1 + (if l.length = 4 then 0 else 1) ≤ w.sum := by
  have hlnil : l ≠ [] := by intro he; subst l; cases h; simp at hw
  have hlen := h.chain_length hlnil
  have hbound := twice_length_le_sum hmin
  have hpos := List.length_pos_iff.mpr hw
  by_cases hl : l.length = 4
  · have hW := amount_profile_eq_two_of_length_four h hl hmin
    simp [selectedChain, hl, List.length_take, hW]
  · have hsel : (selectedChain Q l).length = w.length := by
      simpa only [selectedChain, hl, ↓reduceIte] using interiorRepresentatives_length h hlast
    simp only [hl, ↓reduceIte, hsel]
    constructor
    · trivial
    · omega

end CycleClique.Construction

end OAI
