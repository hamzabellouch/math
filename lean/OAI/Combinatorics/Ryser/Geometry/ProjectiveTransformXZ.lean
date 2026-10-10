import OAI.Combinatorics.Ryser.Geometry.ProjectiveTransformBasic

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

noncomputable def swapXZPoint : ProjectivePoint F → ProjectivePoint F := by
  classical
  exact fun p => match p with
    | Sum.inl (x, y) =>
        if x = 0 then Sum.inr (some y) else Sum.inl (1 / x, y / x)
    | Sum.inr none => Sum.inr none
    | Sum.inr (some a) => Sum.inl (0, a)

noncomputable def swapXZLine : ProjectiveLine F → ProjectiveLine F := by
  classical
  exact fun l => match l with
    | none => some (none, 0)
    | some (none, c) => if c = 0 then none else some (none, 1 / c)
    | some (some a, b) => some (some b, a)

@[simp] theorem swapXZPoint_finite_zero (y : F) :
    swapXZPoint (Sum.inl (0, y)) = Sum.inr (some y) := by
  classical
  simp [swapXZPoint]

theorem swapXZPoint_finite_of_ne_zero (x y : F) (hx : x ≠ 0) :
    swapXZPoint (Sum.inl (x, y)) = Sum.inl (1 / x, y / x) := by
  classical
  simp [swapXZPoint, hx]

@[simp] theorem swapXZPoint_infinite_slope (a : F) :
    swapXZPoint (Sum.inr (some a)) = Sum.inl (0, a) := rfl

@[simp] theorem swapXZPoint_infinite_vertical :
    swapXZPoint (Sum.inr (none : Direction F)) = Sum.inr none := rfl

@[simp] theorem swapXZLine_infinity :
    swapXZLine (none : ProjectiveLine F) = some (none, 0) := rfl

@[simp] theorem swapXZLine_vertical_zero :
    swapXZLine (some (none, (0 : F))) = none := by
  classical
  simp [swapXZLine]

theorem swapXZLine_vertical_of_ne_zero (c : F) (hc : c ≠ 0) :
    swapXZLine (some (none, c)) = some (none, 1 / c) := by
  classical
  simp [swapXZLine, hc]

@[simp] theorem swapXZLine_sloped (a b : F) :
    swapXZLine (some (some a, b)) = some (some b, a) := rfl

theorem swapXZPoint_involutive : Function.Involutive (swapXZPoint (F := F)) := by
  classical
  intro p
  cases p with
  | inl p =>
    rcases p with ⟨x, y⟩
    by_cases hx : x = 0
    · subst x
      simp [swapXZPoint]
    · have hy : y / x / (1 / x) = y := by
        simpa only [div_one] using div_div_div_cancel_right₀ hx y (1 : F)
      simp [swapXZPoint, hx]
  | inr d =>
    cases d <;> simp [swapXZPoint]

theorem swapXZLine_involutive : Function.Involutive (swapXZLine (F := F)) := by
  classical
  intro l
  cases l with
  | none => simp [swapXZLine]
  | some l =>
    rcases l with ⟨d, c⟩
    cases d with
    | none =>
      by_cases hc : c = 0
      · subst c
        simp [swapXZLine]
      · simp [swapXZLine, hc]
    | some a => rfl

theorem swapXZ_incidence (p : ProjectivePoint F) (l : ProjectiveLine F) :
    ProjectiveIncidence (swapXZPoint p) (swapXZLine l) ↔
      ProjectiveIncidence p l := by
  classical
  cases p with
  | inl p =>
    rcases p with ⟨x, y⟩
    cases l with
    | none =>
      by_cases hx : x = 0
      · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, hx]
      · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
          hx]
    | some l =>
      rcases l with ⟨d, b⟩
      cases d with
      | none =>
        by_cases hx : x = 0
        · by_cases hb : b = 0
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
              hx, hb]
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
              hx, hb, Ne.symm hb]
        · by_cases hb : b = 0
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
              hx, hb]
          · simp only [swapXZPoint, ite_eq_right hx, swapXZLine, ite_eq_right hb,
              ProjectiveIncidence, Incidence, projection]
            exact ⟨eq_of_one_div_eq_one_div,
              fun h => congrArg (fun c : F => 1 / c) h⟩
      | some a =>
        by_cases hx : x = 0
        · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection, hx]
        · simp only [swapXZPoint, ite_eq_right hx, swapXZLine,
            ProjectiveIncidence, Incidence, projection]
          rw [mul_one_div, ← sub_div, div_eq_iff hx,
            sub_eq_iff_eq_add, sub_eq_iff_eq_add, add_comm (a * x) b]
  | inr d =>
    cases d with
    | none =>
      cases l with
      | none => simp [swapXZPoint, swapXZLine, ProjectiveIncidence]
      | some l =>
        rcases l with ⟨d, c⟩
        cases d with
        | none =>
          by_cases hc : c = 0 <;>
            simp [swapXZPoint, swapXZLine, ProjectiveIncidence, hc]
        | some a => simp [swapXZPoint, swapXZLine, ProjectiveIncidence]
    | some a =>
      cases l with
      | none => simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection]
      | some l =>
        rcases l with ⟨d, c⟩
        cases d with
        | none =>
          by_cases hc : c = 0
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, hc]
          · simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection,
              hc, Ne.symm hc]
        | some b =>
          simp [swapXZPoint, swapXZLine, ProjectiveIncidence, Incidence, projection]

noncomputable def swapXZ (F : Type*) [Field F] : ProjectiveTransform F where
  points :=
    { toFun := swapXZPoint
      invFun := swapXZPoint
      left_inv := swapXZPoint_involutive
      right_inv := swapXZPoint_involutive }
  lines :=
    { toFun := swapXZLine
      invFun := swapXZLine
      left_inv := swapXZLine_involutive
      right_inv := swapXZLine_involutive }
  incidence := swapXZ_incidence

@[simp] theorem swapXZ_points (p : ProjectivePoint F) :
    (swapXZ F).points p = swapXZPoint p := rfl

@[simp] theorem swapXZ_lines (l : ProjectiveLine F) :
    (swapXZ F).lines l = swapXZLine l := rfl

@[simp] theorem swapXZ_points_finite_zero (y : F) :
    (swapXZ F).points (Sum.inl (0, y)) = Sum.inr (some y) :=
  swapXZPoint_finite_zero y

theorem swapXZ_points_finite_of_ne_zero (x y : F) (hx : x ≠ 0) :
    (swapXZ F).points (Sum.inl (x, y)) = Sum.inl (1 / x, y / x) :=
  swapXZPoint_finite_of_ne_zero x y hx

@[simp] theorem swapXZ_points_infinite_slope (a : F) :
    (swapXZ F).points (Sum.inr (some a)) = Sum.inl (0, a) := rfl

@[simp] theorem swapXZ_points_infinite_vertical :
    (swapXZ F).points (Sum.inr none) = Sum.inr none := rfl

@[simp] theorem swapXZ_lines_infinity :
    (swapXZ F).lines none = some (none, 0) := rfl

@[simp] theorem swapXZ_lines_vertical_zero :
    (swapXZ F).lines (some (none, 0)) = none :=
  swapXZLine_vertical_zero

theorem swapXZ_lines_vertical_of_ne_zero (c : F) (hc : c ≠ 0) :
    (swapXZ F).lines (some (none, c)) = some (none, 1 / c) :=
  swapXZLine_vertical_of_ne_zero c hc

@[simp] theorem swapXZ_lines_sloped (a b : F) :
    (swapXZ F).lines (some (some a, b)) = some (some b, a) := rfl

end RyserCoveringCounterexample

end OAI
