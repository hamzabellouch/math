import OAI.Probability.SwitchChain.DisjointCellCounting
import OAI.Probability.SwitchChain.CrossCellMoments
import OAI.Probability.SwitchChain.PairFibers

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]
open DisjointEncoding

def jointMomentEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    JointData e G ≃ CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
      (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) where
  toFun z := ⟨(z.2.2.val, z.1, z.2.1), z.2.2.property⟩
  invFun z := ⟨z.val.2.1, z.val.2.2, z.val.1, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def degreeCellMomentEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
      (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) :=
  (degreeCellJointEquiv e G).trans (jointMomentEquiv e G)

@[simp] theorem degreeCellMomentEquiv_left (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (H : DegreeCell e G) :
    (degreeCellMomentEquiv e G H).val.2.1 = leftData e G (cellEncode e G H) := rfl

@[simp] theorem degreeCellMomentEquiv_right (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (H : DegreeCell e G) :
    (degreeCellMomentEquiv e G H).val.2.2 = rightData e G (cellEncode e G H) := rfl

theorem sum_degreeCell_left_fiber (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (x : LeftData e G) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      if leftData e G (cellEncode e G H) = x then
        g (rightData e G (cellEncode e G H)) else 0) =
    ∑ y : RightData e G,
      (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ) * g y := by
  calc
    _ = ∑ z : CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
        (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1),
        if z.val.2.1 = x then g z.val.2.2 else 0 :=
      (degreeCellMomentEquiv e G).sum_comp _
    _ = _ := by
      have h := CrossCellMoments.sum_first_fiber (CrossBlock.total (crossCode e G))
        (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) x g
      refine Eq.trans ?_ h
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> rfl

def conditionalRightDegreeCell (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (x : LeftData e G) (g : RightData e G → ℝ) : ℝ :=
  (∑ H : DegreeCell e G,
    if leftData e G (cellEncode e G H) = x then
      g (rightData e G (cellEncode e G H)) else 0) /
  (∑ H : DegreeCell e G,
    if leftData e G (cellEncode e G H) = x then (1 : ℝ) else 0)

theorem conditionalRightDegreeCell_eq (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (x : LeftData e G) (g : RightData e G → ℝ) :
    conditionalRightDegreeCell e G x g =
      CrossCellMoments.conditionalRight (CrossBlock.total (crossCode e G))
        (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) x g := by
  rw [CrossCellMoments.conditionalRight_eq_table]
  unfold conditionalRightDegreeCell
  rw [sum_degreeCell_left_fiber]
  have h := sum_degreeCell_left_fiber e G x (fun _ => 1)
  simp only [mul_one] at h
  rw [h]

theorem conditionalRightDegreeCell_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (hs : CrossBlock.total (crossCode e G) = 2)
    (x : LeftData e G) (g : RightData e G → ℝ) :
    conditionalRightDegreeCell e G x g =
      CrossCovariance.rightSliceAverage (fun _ : RightData e G => 1)
        (fun y => flag y.val.1) (flag x.val.1) g := by
  rw [conditionalRightDegreeCell_eq, hs, CrossCellMoments.conditionalRight_two]
  rfl

theorem expectation_rightObservable (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (g : RightData e G → ℝ) (H : DegreeCell e G) :
    PairFibers.expectation
      (Setoid.ker (fun K : DegreeCell e G => leftData e G (cellEncode e G K)))
      (WithLp.toLp 2 (fun K => g (rightData e G (cellEncode e G K)))) H =
      conditionalRightDegreeCell e G (leftData e G (cellEncode e G H)) g := by
  rw [PairFibers.expectation_apply]
  unfold conditionalRightDegreeCell PairFibers.cell
  simp only [Finset.sum_filter]
  congr 1
  · apply Finset.sum_congr rfl
    intro K hK
    by_cases h : leftData e G (cellEncode e G K) = leftData e G (cellEncode e G H)
    · simp [h]
    · simp [h, Ne.symm h]
  · simp only [Finset.sum_boole]
    congr 2
    ext K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact eq_comm

theorem expectation_rightObservable_two_span (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (hs : CrossBlock.total (crossCode e G) = 2) (g : RightData e G → ℝ) :
    ∃ A B : ℝ, ∀ H : DegreeCell e G,
      PairFibers.expectation
        (Setoid.ker (fun K : DegreeCell e G => leftData e G (cellEncode e G K)))
        (WithLp.toLp 2 (fun K => g (rightData e G (cellEncode e G K)))) H =
      A + B * flag (leftData e G (cellEncode e G H)).val.1 := by
  refine ⟨CrossCovariance.rightSliceAverage (fun _ : RightData e G => 1)
      (fun y => flag y.val.1) 0 g,
    CrossCovariance.rightSliceAverage (fun _ : RightData e G => 1)
      (fun y => flag y.val.1) 1 g -
      CrossCovariance.rightSliceAverage (fun _ : RightData e G => 1)
        (fun y => flag y.val.1) 0 g, ?_⟩
  intro H
  rw [expectation_rightObservable, conditionalRightDegreeCell_two e G hs]
  exact CrossCovariance.rightSliceAverage_span (fun _ : RightData e G => 1)
    (fun x : LeftData e G => flag x.val.1) (fun y => flag y.val.1)
    (fun x => flag_zero_or_one x.val.1) g (leftData e G (cellEncode e G H))

theorem sum_degreeCell_right_fiber (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (x : RightData e G) (g : LeftData e G → ℝ) :
    (∑ H : DegreeCell e G,
      if rightData e G (cellEncode e G H) = x then
        g (leftData e G (cellEncode e G H)) else 0) =
    ∑ y : LeftData e G,
      (CrossBlock.count (CrossBlock.total (crossCode e G)) y.val.1 x.val.1 : ℝ) * g y := by
  calc
    _ = ∑ z : CrossCellMoments.Cell (CrossBlock.total (crossCode e G))
        (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1),
        if z.val.2.2 = x then g z.val.2.1 else 0 :=
      (degreeCellMomentEquiv e G).sum_comp _
    _ = _ := by
      have h := CrossCellMoments.sum_second_fiber (CrossBlock.total (crossCode e G))
        (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) x g
      refine Eq.trans ?_ h
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> rfl

def conditionalLeftDegreeCell (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (x : RightData e G) (g : LeftData e G → ℝ) : ℝ :=
  (∑ H : DegreeCell e G,
    if rightData e G (cellEncode e G H) = x then
      g (leftData e G (cellEncode e G H)) else 0) /
  (∑ H : DegreeCell e G,
    if rightData e G (cellEncode e G H) = x then (1 : ℝ) else 0)

theorem conditionalLeftDegreeCell_eq (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (x : RightData e G) (g : LeftData e G → ℝ) :
    conditionalLeftDegreeCell e G x g =
      CrossCellMoments.conditionalLeft (CrossBlock.total (crossCode e G))
        (fun x : LeftData e G => x.val.1) (fun y : RightData e G => y.val.1) x g := by
  rw [CrossCellMoments.conditionalLeft_eq_table]
  unfold conditionalLeftDegreeCell
  rw [sum_degreeCell_right_fiber]
  have h := sum_degreeCell_right_fiber e G x (fun _ => 1)
  simp only [mul_one] at h
  rw [h]

theorem conditionalLeftDegreeCell_two (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (hs : CrossBlock.total (crossCode e G) = 2)
    (x : RightData e G) (g : LeftData e G → ℝ) :
    conditionalLeftDegreeCell e G x g =
      CrossCovariance.rightSliceAverage (fun _ : LeftData e G => 1)
        (fun y => flag y.val.1) (flag x.val.1) g := by
  rw [conditionalLeftDegreeCell_eq, hs, CrossCellMoments.conditionalLeft_two]
  rfl

theorem expectation_leftObservable (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (g : LeftData e G → ℝ) (H : DegreeCell e G) :
    PairFibers.expectation
      (Setoid.ker (fun K : DegreeCell e G => rightData e G (cellEncode e G K)))
      (WithLp.toLp 2 (fun K => g (leftData e G (cellEncode e G K)))) H =
      conditionalLeftDegreeCell e G (rightData e G (cellEncode e G H)) g := by
  rw [PairFibers.expectation_apply]
  unfold conditionalLeftDegreeCell PairFibers.cell
  simp only [Finset.sum_filter]
  congr 1
  · apply Finset.sum_congr rfl
    intro K hK
    by_cases h : rightData e G (cellEncode e G K) = rightData e G (cellEncode e G H)
    · simp [h]
    · simp [h, Ne.symm h]
  · simp only [Finset.sum_boole]
    congr 2
    ext K
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact eq_comm

theorem expectation_leftObservable_two_span (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (hs : CrossBlock.total (crossCode e G) = 2) (g : LeftData e G → ℝ) :
    ∃ A B : ℝ, ∀ H : DegreeCell e G,
      PairFibers.expectation
        (Setoid.ker (fun K : DegreeCell e G => rightData e G (cellEncode e G K)))
        (WithLp.toLp 2 (fun K => g (leftData e G (cellEncode e G K)))) H =
      A + B * flag (rightData e G (cellEncode e G H)).val.1 := by
  refine ⟨CrossCovariance.rightSliceAverage (fun _ : LeftData e G => 1)
      (fun y => flag y.val.1) 0 g,
    CrossCovariance.rightSliceAverage (fun _ : LeftData e G => 1)
      (fun y => flag y.val.1) 1 g -
      CrossCovariance.rightSliceAverage (fun _ : LeftData e G => 1)
        (fun y => flag y.val.1) 0 g, ?_⟩
  intro H
  rw [expectation_leftObservable, conditionalLeftDegreeCell_two e G hs]
  exact CrossCovariance.rightSliceAverage_span (fun _ : LeftData e G => 1)
    (fun x : RightData e G => flag x.val.1) (fun y => flag y.val.1)
    (fun x => flag_zero_or_one x.val.1) g (rightData e G (cellEncode e G H))

end Problem315.DisjointMarginal

end

end OAI
