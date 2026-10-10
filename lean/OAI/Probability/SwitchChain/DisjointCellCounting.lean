import OAI.Probability.SwitchChain.DisjointCoordinateFeasibility
import OAI.Probability.SwitchChain.CrossCovariance

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal

variable {V : Type*} [Fintype V]
open DisjointEncoding

abbrev MarginData {α : Type*} [Fintype α] (A : Finset α) (q : Nat) :=
  {x : Fin 3 × Finset α // x.2 ⊆ A ∧ x.1.val + x.2.card = q}

abbrev LeftData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  MarginData (BinaryAssignments.singletons (leftCounts e G))
    (CrossBlock.row (crossCode e G) 0 + (leftAssignment e G G).card)

abbrev RightData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  MarginData (BinaryAssignments.singletons (rightCounts e G))
    (CrossBlock.col (crossCode e G) 0 + (rightAssignment e G G).card)

abbrev MatrixFiber (s : Nat) (r c : Fin 3) :=
  {M : CrossBlock.Matrix // CrossBlock.total M = s ∧
    CrossBlock.row M 0 = r.val ∧ CrossBlock.col M 0 = c.val}

abbrev JointData (e : Fin 4 ↪ V) (G : SimpleGraph V) :=
  Σ x : LeftData e G, Σ y : RightData e G,
    MatrixFiber (CrossBlock.total (crossCode e G)) x.val.1 y.val.1

def leftData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    LeftData e G :=
  ⟨(⟨CrossBlock.row c.matrix 0, by have := CrossBlock.row_le_two c.matrix 0; omega⟩, c.left),
    c.left_subset,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).2.1⟩

def rightData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    RightData e G :=
  ⟨(⟨CrossBlock.col c.matrix 0, by have := CrossBlock.col_le_two c.matrix 0; omega⟩, c.right),
    c.right_subset,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).2.2⟩

def toJointData (e : Fin 4 ↪ V) (G : SimpleGraph V) (c : FeasibleCoordinates e G) :
    JointData e G :=
  ⟨leftData e G c, rightData e G c, c.matrix,
    ((coordinate_degrees_iff e G c.matrix c.left c.right c.left_subset c.right_subset).mp
      c.degrees).1, rfl, rfl⟩

def fromJointData (e : Fin 4 ↪ V) (G : SimpleGraph V) (z : JointData e G) :
    FeasibleCoordinates e G where
  matrix := z.2.2.val
  left := z.1.val.2
  right := z.2.1.val.2
  left_subset := z.1.property.1
  right_subset := z.2.1.property.1
  degrees := by
    apply (coordinate_degrees_iff e G _ _ _ z.1.property.1 z.2.1.property.1).mpr
    exact ⟨z.2.2.property.1,
      by rw [z.2.2.property.2.1]; exact z.1.property.2,
      by rw [z.2.2.property.2.2]; exact z.2.1.property.2⟩

def coordinatesEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    FeasibleCoordinates e G ≃ JointData e G where
  toFun := toJointData e G
  invFun := fromJointData e G
  left_inv c := by ext <;> rfl
  right_inv z := by
    rcases z with ⟨⟨⟨⟨r,hrlt⟩,U⟩,hU⟩, ⟨⟨⟨c,hclt⟩,W⟩,hW⟩, M, hs, hr, hc⟩
    dsimp only at hr hc
    subst r
    subst c
    rfl

def degreeCellJointEquiv (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    DegreeCell e G ≃ JointData e G :=
  (degreeCellEquiv e G).trans (coordinatesEquiv e G)

theorem matrixFiber_card (s : Nat) (r c : Fin 3) :
    Fintype.card (MatrixFiber s r c) = CrossBlock.count s r c := by
  simp only [MatrixFiber, Fintype.card_subtype, CrossBlock.count]

theorem sum_degreeCell_joint
    (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (f : LeftData e G → ℝ) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      f (leftData e G (cellEncode e G H)) * g (rightData e G (cellEncode e G H))) =
    ∑ x : LeftData e G, ∑ y : RightData e G,
      (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ) *
        f x * g y := by
  calc
    _ = ∑ z : JointData e G, f z.1 * g z.2.1 := by
      exact (degreeCellJointEquiv e G).sum_comp (fun z => f z.1 * g z.2.1)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, matrixFiber_card]
      ring

theorem card_degreeCell_eq_sum_count (e : Fin 4 ↪ V) (G : SimpleGraph V) :
    (Fintype.card (DegreeCell e G) : ℝ) =
      ∑ x : LeftData e G, ∑ y : RightData e G,
        (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ) := by
  simpa using sum_degreeCell_joint e G (fun _ => 1) (fun _ => 1)

theorem average_degreeCell_joint
    (e : Fin 4 ↪ V) (G : SimpleGraph V)
    (f : LeftData e G → ℝ) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      f (leftData e G (cellEncode e G H)) * g (rightData e G (cellEncode e G H))) /
        (Fintype.card (DegreeCell e G) : ℝ) =
    (∑ x : LeftData e G, ∑ y : RightData e G,
      (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ) *
        f x * g y) /
      (∑ x : LeftData e G, ∑ y : RightData e G,
        (CrossBlock.count (CrossBlock.total (crossCode e G)) x.val.1 y.val.1 : ℝ)) := by
  rw [sum_degreeCell_joint, card_degreeCell_eq_sum_count]

def flag (r : Fin 3) : ℝ := if r = 1 then 0 else 1

theorem flag_zero_or_one (r : Fin 3) : flag r = 0 ∨ flag r = 1 := by
  unfold flag
  split_ifs <;> simp

theorem sum_degreeCell_joint_two
    (e : Fin 4 ↪ V) (G : SimpleGraph V) (hs : CrossBlock.total (crossCode e G) = 2)
    (f : LeftData e G → ℝ) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      f (leftData e G (cellEncode e G H)) * g (rightData e G (cellEncode e G H))) =
    CrossCovariance.jointMoment (fun _ : LeftData e G => 1)
      (fun _ : RightData e G => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) f g := by
  rw [sum_degreeCell_joint, hs]
  unfold CrossCovariance.jointMoment
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [CrossBlock.count_two_real]
  simp only [flag, one_mul]

theorem card_degreeCell_eq_mass_two
    (e : Fin 4 ↪ V) (G : SimpleGraph V) (hs : CrossBlock.total (crossCode e G) = 2) :
    (Fintype.card (DegreeCell e G) : ℝ) =
    CrossCovariance.mass (fun _ : LeftData e G => 1)
      (fun _ : RightData e G => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) := by
  simpa only [CrossCovariance.mass, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using sum_degreeCell_joint_two e G hs (fun _ => 1) (fun _ => 1)

theorem average_degreeCell_joint_two
    (e : Fin 4 ↪ V) (G : SimpleGraph V) (hs : CrossBlock.total (crossCode e G) = 2)
    (f : LeftData e G → ℝ) (g : RightData e G → ℝ) :
    (∑ H : DegreeCell e G,
      f (leftData e G (cellEncode e G H)) * g (rightData e G (cellEncode e G H))) /
        (Fintype.card (DegreeCell e G) : ℝ) =
    CrossCovariance.jointAverage (fun _ : LeftData e G => 1)
      (fun _ : RightData e G => 1) (fun x => flag x.val.1) (fun y => flag y.val.1) f g := by
  rw [sum_degreeCell_joint_two e G hs, card_degreeCell_eq_mass_two e G hs]
  rfl

end Problem315.DisjointMarginal

end

end OAI
