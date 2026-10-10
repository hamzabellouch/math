import OAI.Combinatorics.Ryser.Geometry.ProjectiveTransformBasic
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

noncomputable def swapXYDirection (d : Direction F) : Direction F := by
  classical
  exact match d with
    | none => some 0
    | some a => if a = 0 then none else some a⁻¹

@[simp] theorem swapXYDirection_none :
    swapXYDirection (none : Direction F) = some 0 := rfl

@[simp] theorem swapXYDirection_zero :
    swapXYDirection (some (0 : F)) = none := by simp [swapXYDirection]

@[simp] theorem swapXYDirection_nonzero (a : F) (ha : a ≠ 0) :
    swapXYDirection (some a) = some a⁻¹ := by simp [swapXYDirection, ha]

theorem swapXYDirection_involutive :
    Function.Involutive (swapXYDirection (F := F)) := by
  classical
  intro d
  cases d with
  | none => simp [swapXYDirection]
  | some a =>
    by_cases ha : a = 0
    · simp [swapXYDirection, ha]
    · simp [swapXYDirection, ha]

noncomputable def swapXYPoint : ProjectivePoint F → ProjectivePoint F
  | Sum.inl p => Sum.inl (p.2, p.1)
  | Sum.inr d => Sum.inr (swapXYDirection d)

theorem swapXYPoint_involutive :
    Function.Involutive (swapXYPoint (F := F)) := by
  intro p
  cases p with
  | inl p => rfl
  | inr d =>
    change Sum.inr (swapXYDirection (swapXYDirection d)) = Sum.inr d
    rw [swapXYDirection_involutive]

noncomputable def swapXYAffineLine (l : AffineLine F) : AffineLine F := by
  classical
  exact match l with
    | (none, b) => (some 0, b)
    | (some a, b) => if a = 0 then (none, b) else (some a⁻¹, -b / a)

@[simp] theorem swapXYAffineLine_direction (l : AffineLine F) :
    (swapXYAffineLine l).1 = swapXYDirection l.1 := by
  classical
  rcases l with ⟨d, b⟩
  cases d with
  | none => rfl
  | some a =>
    by_cases ha : a = 0 <;> simp [swapXYAffineLine, swapXYDirection, ha]

theorem swapXYAffineLine_involutive :
    Function.Involutive (swapXYAffineLine (F := F)) := by
  classical
  rintro ⟨d, b⟩
  cases d with
  | none => simp [swapXYAffineLine]
  | some a =>
    by_cases ha : a = 0
    · simp [swapXYAffineLine, ha]
    · simp [swapXYAffineLine, ha, div_eq_mul_inv]

noncomputable def swapXYLine : ProjectiveLine F → ProjectiveLine F
  | none => none
  | some l => some (swapXYAffineLine l)

theorem swapXYLine_involutive :
    Function.Involutive (swapXYLine (F := F)) := by
  intro l
  cases l with
  | none => rfl
  | some l =>
    change some (swapXYAffineLine (swapXYAffineLine l)) = some l
    rw [swapXYAffineLine_involutive]

private theorem swapXY_projection_equation (a b x y : F) (ha : a ≠ 0) :
    (x - a⁻¹ * y = -b / a) ↔ (y - a * x = b) := by
  have hrewrite : x - a⁻¹ * y = -(y - a * x) / a := by
    field_simp [ha]; ring
  rw [hrewrite, div_left_inj' ha]
  exact neg_inj

theorem swapXY_affine_incidence (p : Point F) (l : AffineLine F) :
    Incidence (p.2, p.1) (swapXYAffineLine l) ↔ Incidence p l := by
  classical
  rcases p with ⟨x, y⟩
  rcases l with ⟨d, b⟩
  cases d with
  | none => simp [swapXYAffineLine, Incidence, projection]
  | some a =>
    by_cases ha : a = 0
    · simp [swapXYAffineLine, Incidence, projection, ha]
    · simpa only [swapXYAffineLine, ite_eq_right ha, Incidence, projection] using
        swapXY_projection_equation a b x y ha

theorem swapXY_incidence (p : ProjectivePoint F) (l : ProjectiveLine F) :
    ProjectiveIncidence (swapXYPoint p) (swapXYLine l) ↔
      ProjectiveIncidence p l := by
  cases p with
  | inl p =>
    cases l with
    | none => rfl
    | some l => exact swapXY_affine_incidence p l
  | inr d =>
    cases l with
    | none => rfl
    | some l =>
      change swapXYDirection d = (swapXYAffineLine l).1 ↔ d = l.1
      rw [swapXYAffineLine_direction]
      exact swapXYDirection_involutive.injective.eq_iff

noncomputable def swapXY (F : Type*) [Field F] : ProjectiveTransform F where
  points :=
    { toFun := swapXYPoint
      invFun := swapXYPoint
      left_inv := swapXYPoint_involutive
      right_inv := swapXYPoint_involutive }
  lines :=
    { toFun := swapXYLine
      invFun := swapXYLine
      left_inv := swapXYLine_involutive
      right_inv := swapXYLine_involutive }
  incidence := swapXY_incidence

@[simp] theorem swapXY_points_finite (p : Point F) :
    (swapXY F).points (Sum.inl p) = Sum.inl (p.2, p.1) := rfl

@[simp] theorem swapXY_points_infinite (d : Direction F) :
    (swapXY F).points (Sum.inr d) = Sum.inr (swapXYDirection d) := rfl

@[simp] theorem swapXY_lines_infinity :
    (swapXY F).lines none = none := rfl

@[simp] theorem swapXY_lines_affine (l : AffineLine F) :
    (swapXY F).lines (some l) = some (swapXYAffineLine l) := rfl

@[simp] theorem swapXY_lines_vertical (b : F) :
    (swapXY F).lines (some (none, b)) = some (some 0, b) := rfl

@[simp] theorem swapXY_lines_slope_zero (b : F) :
    (swapXY F).lines (some (some 0, b)) = some (none, b) := by
  rw [swapXY_lines_affine]
  simp [swapXYAffineLine]

@[simp] theorem swapXY_lines_slope_nonzero (a b : F) (ha : a ≠ 0) :
    (swapXY F).lines (some (some a, b)) = some (some a⁻¹, -b / a) := by
  rw [swapXY_lines_affine]
  simp [swapXYAffineLine, ha]

end RyserCoveringCounterexample

end OAI
