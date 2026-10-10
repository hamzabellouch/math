import OAI.Combinatorics.ContingencyTables.Dense.GridAdjacency
import OAI.Combinatorics.ContingencyTables.Dense.GridMass

namespace OAI

/-! # From geometric cut faces to Metropolis cut flow -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

noncomputable section

variable {q K : ℕ}

private theorem edge_not_reverse (a b : Grid (I := Fin q) K) (i j : Fin q)
    (hi : IsGridEdge (a, b, i)) (hj : IsGridEdge (b, a, j)) : False := by
  by_cases h : i = j
  · subst j
    have ha : corner b i = corner a i + 1 := hi.1
    have hb : corner a i = corner b i + 1 := hj.1
    omega
  · have heq : corner a i = corner b i := congrArg Subtype.val (hj.2 i h)
    have hplus : corner b i = corner a i + 1 := hi.1
    omega

private theorem cutEdge_eq {Q : (Fin q → ℤ) → Prop} (e f : CutEdge K Q)
    (ha : e.val.1 = f.val.1) (hb : e.val.2.1 = f.val.2.1) : e = f := by
  have hi : e.val.2.2 = f.val.2.2 := by
    apply edge_axis_unique e.val.1 e.val.2.1 _ _ e.property.1
    rw [ha, hb]
    exact f.property.1
  apply Subtype.ext
  exact Prod.ext ha (Prod.ext hb hi)

def cutPair (Q : (Fin q → ℤ) → Prop) (e : CutEdge K Q) :
    Selected K Q × Selected K (fun a => ¬ Q a) :=
  if h : Q (corner e.val.1) then
    (⟨e.val.1, h⟩, ⟨e.val.2.1, e.property.2.mp h⟩)
  else
    (⟨e.val.2.1, by
      by_contra hn
      exact h (e.property.2.mpr hn)⟩, ⟨e.val.1, h⟩)

theorem cutPair_neighbor (Q : (Fin q → ℤ) → Prop) (e : CutEdge K Q) :
    Neighbor (cutPair Q e).1.val (cutPair Q e).2.val := by
  unfold cutPair
  split_ifs
  · exact ⟨e.val.2.2, true, e.property.1⟩
  · exact ⟨e.val.2.2, false, e.property.1⟩

theorem cutPair_weight (Q : (Fin q → ℤ) → Prop) (w : Grid (I := Fin q) K → ℝ)
    (e : CutEdge K Q) :
    min (w (cutPair Q e).1.val) (w (cutPair Q e).2.val) =
      min (w e.val.1) (w e.val.2.1) := by
  unfold cutPair
  split_ifs <;> simp only [min_comm]

theorem cutPair_injective (Q : (Fin q → ℤ) → Prop) : Function.Injective (cutPair (K := K) Q) := by
  intro e f h
  have hp := congrArg (fun p : Selected K Q × Selected K (fun a => ¬ Q a) => p.1.val) h
  have hn := congrArg (fun p : Selected K Q × Selected K (fun a => ¬ Q a) => p.2.val) h
  by_cases he : Q (corner e.val.1) <;> by_cases hf : Q (corner f.val.1)
  · simp only [cutPair, dite_eq_left he, dite_eq_left hf] at hp hn
    exact cutEdge_eq e f hp hn
  · simp only [cutPair, dite_eq_left he, dite_eq_right hf] at hp hn
    exfalso
    apply edge_not_reverse e.val.1 e.val.2.1 e.val.2.2 f.val.2.2 e.property.1
    rw [hp, hn]
    exact f.property.1
  · simp only [cutPair, dite_eq_right he, dite_eq_left hf] at hp hn
    exfalso
    apply edge_not_reverse e.val.1 e.val.2.1 e.val.2.2 f.val.2.2 e.property.1
    rw [hp, hn]
    exact f.property.1
  · simp only [cutPair, dite_eq_right he, dite_eq_right hf] at hp hn
    exact cutEdge_eq e f hn hp

theorem selected_sum_eq_filter (Q : (Fin q → ℤ) → Prop) (f : Grid (I := Fin q) K → ℝ) :
    (∑ a : Selected K Q, f a.val) = ∑ a ∈ Finset.univ.filter (fun a => Q (corner a)), f a := by
  exact (Finset.sum_subtype (p := fun a : Grid (I := Fin q) K => Q (corner a))
    (F := instFintypeSelected Q) (Finset.univ.filter (fun a => Q (corner a)))
    (fun a => by simp) f).symm

/-- Every geometric cut face contributes its weight once to the actual
ordered cut flow. An injection suffices; no exterior or duplicate face is
counted in the conductance lower bound. -/
theorem cut_faces_le_neighbor_flow (Q : (Fin q → ℤ) → Prop)
    (w : Grid (I := Fin q) K → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (∑ e : CutEdge K Q, min (w e.val.1) (w e.val.2.1)) ≤
      ∑ a ∈ Finset.univ.filter (fun a : Grid (I := Fin q) K => Q (corner a)),
        ∑ b ∈ Finset.univ.filter (fun b : Grid (I := Fin q) K => ¬ Q (corner b)),
          if Neighbor a b then min (w a) (w b) else 0 := by
  calc
    _ ≤ ∑ p : Selected K Q × Selected K (fun a => ¬ Q a),
        if Neighbor p.1.val p.2.val then min (w p.1.val) (w p.2.val) else 0 := by
      apply Finset.sum_le_sum_of_injOn (cutPair Q) (cutPair_injective Q).injOn (Finset.subset_univ _)
      · intro e _
        rw [ite_eq_left (cutPair_neighbor Q e), cutPair_weight]
      · intro p _ _
        split_ifs
        · exact le_min (hw _) (hw _)
        · exact le_rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      change (∑ a : Selected K Q, ∑ b : Selected K (fun a => ¬ Q a),
        if Neighbor a.val b.val then min (w a.val) (w b.val) else 0) = _
      rw [selected_sum_eq_filter Q (fun a => ∑ b : Selected K (fun a => ¬ Q a),
        if Neighbor a b.val then min (w a) (w b.val) else 0)]
      apply Finset.sum_congr rfl
      intro a _
      convert selected_sum_eq_filter (fun a => ¬ Q a)
        (fun b => if Neighbor a b then min (w a) (w b) else 0) using 1
      congr 1
      ext b
      simp

end

end ContingencyTables.GridBoundary

end OAI
