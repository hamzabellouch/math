import OAI.Probability.SwitchChain.DisjointCellCounting
import OAI.Probability.SwitchChain.DisjointStateCell
import OAI.Probability.SwitchChain.DisjointFiberCell
import OAI.Probability.SwitchChain.DisjointFiberCoordinates

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal
open DisjointEncoding

theorem marginData_eq_iff_subset_eq {α : Type*} [Fintype α]
    {A : Finset α} {q : Nat} (x y : MarginData A q) :
    x = y ↔ x.val.2 = y.val.2 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hx := x.property.2
      have hy := y.property.2
      rw [h] at hx
      omega
    · exact h

variable {n : Nat} {d : Fin n → Nat}

abbrev StateCell (e : Fin 4 ↪ Fin n) (G : GraphState n d) :=
  {H : GraphState n d // SameCell e G.val H.val}

instance stateCellNonempty (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    Nonempty (StateCell e G) := ⟨⟨G, SameCell.refl e G.val⟩⟩

def stateLeftData (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    LeftData e G.val := leftData e G.val (graphStateCellEquiv e G H)

def stateRightData (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    RightData e G.val := rightData e G.val (graphStateCellEquiv e G H)

@[simp] theorem stateLeftData_subset (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) : (stateLeftData e G H).val.2 = leftAssignment e G.val H.val.val := rfl

@[simp] theorem stateRightData_subset (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) : (stateRightData e G H).val.2 = rightAssignment e G.val H.val.val := rfl

theorem sameFiber_left_iff_stateRightData_eq
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H K : StateCell e G) :
    PairResampling.SameFiber {e 0,e 1} H.val.val K.val.val ↔
      stateRightData e G H = stateRightData e G K := by
  rw [marginData_eq_iff_subset_eq, stateRightData_subset, stateRightData_subset]
  exact sameFiber_left_iff_rightAssignment_eq e G H.val K.val H.property K.property

theorem sameFiber_right_iff_stateLeftData_eq
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H K : StateCell e G) :
    PairResampling.SameFiber {e 2,e 3} H.val.val K.val.val ↔
      stateLeftData e G H = stateLeftData e G K := by
  rw [marginData_eq_iff_subset_eq, stateLeftData_subset, stateLeftData_subset]
  exact sameFiber_right_iff_leftAssignment_eq e G H.val K.val H.property K.property

theorem stateCell_of_leftFiber
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G)
    (K : GraphState n d) (h : PairResampling.SameFiber {e 0,e 1} H.val.val K.val) :
    SameCell e G.val K.val :=
  H.property.trans (sameCell_of_leftFiber e H.val.val K.val h)

theorem stateCell_of_rightFiber
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G)
    (K : GraphState n d) (h : PairResampling.SameFiber {e 2,e 3} H.val.val K.val) :
    SameCell e G.val K.val :=
  H.property.trans (sameCell_of_rightFiber e H.val.val K.val h)

def stateCellJointEquiv (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    StateCell e G ≃ JointData e G.val :=
  (stateCellToDegreeCell e G).trans (degreeCellJointEquiv e G.val)

theorem stateCell_card_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    Fintype.card (StateCell e G) = Fintype.card (DegreeCell e G.val) :=
  Fintype.card_congr (stateCellToDegreeCell e G)

theorem sum_stateCell_joint
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : LeftData e G.val → ℝ) (g : RightData e G.val → ℝ) :
    (∑ H : StateCell e G, f (stateLeftData e G H) * g (stateRightData e G H)) =
    ∑ x : LeftData e G.val, ∑ y : RightData e G.val,
      (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ) *
        f x * g y := by
  calc
    _ = ∑ z : JointData e G.val, f z.1 * g z.2.1 :=
      (stateCellJointEquiv e G).sum_comp _
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, matrixFiber_card]
      ring

theorem stateCell_card_eq_sum_count (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    (Fintype.card (StateCell e G) : ℝ) =
      ∑ x : LeftData e G.val, ∑ y : RightData e G.val,
        (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ) := by
  simpa using sum_stateCell_joint e G (fun _ => 1) (fun _ => 1)

theorem average_stateCell_joint
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : LeftData e G.val → ℝ) (g : RightData e G.val → ℝ) :
    (∑ H : StateCell e G, f (stateLeftData e G H) * g (stateRightData e G H)) /
        (Fintype.card (StateCell e G) : ℝ) =
    (∑ x : LeftData e G.val, ∑ y : RightData e G.val,
      (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ) *
        f x * g y) /
      (∑ x : LeftData e G.val, ∑ y : RightData e G.val,
        (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ)) := by
  rw [sum_stateCell_joint, stateCell_card_eq_sum_count]

theorem average_stateCell_joint_two
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2)
    (f : LeftData e G.val → ℝ) (g : RightData e G.val → ℝ) :
    (∑ H : StateCell e G, f (stateLeftData e G H) * g (stateRightData e G H)) /
        (Fintype.card (StateCell e G) : ℝ) =
    CrossCovariance.jointAverage (fun _ : LeftData e G.val => 1)
      (fun _ : RightData e G.val => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) f g := by
  rw [average_stateCell_joint]
  unfold CrossCovariance.jointAverage CrossCovariance.mass CrossCovariance.jointMoment
  rw [hs]
  simp only [CrossBlock.count_two_real, flag, one_mul, mul_one]

theorem stateCell_joint_fiber_card
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (x : LeftData e G.val) (y : RightData e G.val) :
    ((Finset.univ : Finset (StateCell e G)).filter
      (fun H => stateLeftData e G H = x ∧ stateRightData e G H = y)).card =
      CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 := by
  have h := sum_stateCell_joint e G
    (fun z => if z = x then (1 : ℝ) else 0)
    (fun z => if z = y then (1 : ℝ) else 0)
  have hc :
      (((Finset.univ : Finset (StateCell e G)).filter
        (fun H => stateLeftData e G H = x ∧ stateRightData e G H = y)).card : ℝ) =
      ∑ H : StateCell e G,
        (if stateLeftData e G H = x then (1 : ℝ) else 0) *
          (if stateRightData e G H = y then (1 : ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro H hH
    by_cases hx : stateLeftData e G H = x <;>
      by_cases hy : stateRightData e G H = y <;> simp [hx,hy]
  rw [← hc] at h
  have hh :
      (((Finset.univ : Finset (StateCell e G)).filter
        (fun H => stateLeftData e G H = x ∧ stateRightData e G H = y)).card : ℝ) =
        (CrossBlock.count (CrossBlock.total (crossCode e G.val)) x.val.1 y.val.1 : ℝ) := by
    simpa [mul_ite] using h
  exact_mod_cast hh

theorem stateCell_card_pos (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    0 < Fintype.card (StateCell e G) := Fintype.card_pos

theorem stateCell_mass_two_pos
    (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (hs : CrossBlock.total (crossCode e G.val) = 2) :
    0 < CrossCovariance.mass (fun _ : LeftData e G.val => 1)
      (fun _ : RightData e G.val => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) := by
  have hcard := stateCell_card_eq_sum_count e G
  rw [hs] at hcard
  have hm : CrossCovariance.mass (fun _ : LeftData e G.val => 1)
      (fun _ : RightData e G.val => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) =
      (Fintype.card (StateCell e G) : ℝ) := by
    rw [hcard]
    simp only [CrossCovariance.mass, CrossCovariance.jointMoment,
      CrossBlock.count_two_real, flag, one_mul, mul_one]
  rw [hm]
  exact_mod_cast stateCell_card_pos e G

end Problem315.DisjointMarginal

end

end OAI
