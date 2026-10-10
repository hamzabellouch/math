import OAI.Combinatorics.ContingencyTables.Dense.GridCover
import Mathlib.Data.Fintype.Card

namespace OAI

/-! # Actual axis neighbours and the `2q` proposal-degree bound -/

namespace ContingencyTables.GridBoundary

open scoped Classical

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] {K : ℕ}

def OrientedNeighbor (a b : Grid (I := I) K) (i : I) (sign : Bool) : Prop :=
  if sign then IsGridEdge (a, b, i) else IsGridEdge (b, a, i)

def Neighbor (a b : Grid (I := I) K) : Prop := ∃ i sign, OrientedNeighbor a b i sign

omit [Fintype I] [DecidableEq I] in
theorem neighbor_symm (a b : Grid (I := I) K) : Neighbor a b ↔ Neighbor b a := by
  constructor <;> rintro ⟨i, sign, h⟩ <;> refine ⟨i, !sign, ?_⟩ <;>
    cases sign <;> exact h

omit [Fintype I] [DecidableEq I] in
theorem neighbor_ne (a b : Grid (I := I) K) (h : Neighbor a b) : a ≠ b := by
  rintro rfl
  obtain ⟨i, sign, hs⟩ := h
  cases sign
  · have hh : corner a i = corner a i + 1 := hs.1
    omega
  · have hh : corner a i = corner a i + 1 := hs.1
    omega

omit [Fintype I] [DecidableEq I] in
private theorem oriented_target_unique (a b c : Grid (I := I) K) (i : I) (sign : Bool)
    (hb : OrientedNeighbor a b i sign) (hc : OrientedNeighbor a c i sign) : b = c := by
  funext j
  apply Subtype.ext
  change corner b j = corner c j
  cases sign <;> change IsGridEdge _ at hb hc
  · by_cases hj : j = i
    · subst j
      have hbi : corner a i = corner b i + 1 := hb.1
      have hci : corner a i = corner c i + 1 := hc.1
      omega
    · have hbj := congrArg Subtype.val (hb.2 j hj)
      have hcj := congrArg Subtype.val (hc.2 j hj)
      exact hbj.symm.trans hcj
  · by_cases hj : j = i
    · subst j
      exact hb.1.trans hc.1.symm
    · have hbj := congrArg Subtype.val (hb.2 j hj)
      have hcj := congrArg Subtype.val (hc.2 j hj)
      exact hbj.trans hcj.symm

def neighborDirection (a : Grid (I := I) K) (b : {b // Neighbor a b}) : I × Bool :=
  ⟨Classical.choose b.property, Classical.choose (Classical.choose_spec b.property)⟩

omit [Fintype I] [DecidableEq I] in
private theorem neighborDirection_spec (a : Grid (I := I) K) (b : {b // Neighbor a b}) :
    OrientedNeighbor a b.val (neighborDirection a b).1 (neighborDirection a b).2 :=
  Classical.choose_spec (Classical.choose_spec b.property)

omit [Fintype I] [DecidableEq I] in
theorem neighborDirection_injective (a : Grid (I := I) K) :
    Function.Injective (neighborDirection a) := by
  intro b c h
  have hi := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  apply Subtype.ext
  apply oriented_target_unique a b.val c.val (neighborDirection a b).1 (neighborDirection a b).2
    (neighborDirection_spec a b)
  simpa only [hi, hs] using neighborDirection_spec a c

theorem neighbor_degree (a : Grid (I := I) K) :
    (Finset.univ.filter (Neighbor a)).card ≤ 2 * Fintype.card I := by
  have h := Fintype.card_le_of_injective (neighborDirection a) (neighborDirection_injective a)
  rw [Fintype.card_subtype] at h
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

omit [Fintype I] [DecidableEq I] in
theorem edge_axis_unique (a b : Grid (I := I) K) (i j : I)
    (hi : IsGridEdge (a, b, i)) (hj : IsGridEdge (a, b, j)) : i = j := by
  by_contra h
  have heq : corner b i = corner a i := congrArg Subtype.val (hj.2 i h)
  have hplus : corner b i = corner a i + 1 := hi.1
  omega

end

end ContingencyTables.GridBoundary

end OAI
