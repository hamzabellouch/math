import OAI.Combinatorics.Ryser.Geometry.ProjectiveTransformBasic

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

private def translatePointMap (u v : F) : ProjectivePoint F → ProjectivePoint F
  | Sum.inl p => Sum.inl (p.1 + u, p.2 + v)
  | Sum.inr d => Sum.inr d

private def translateLineMap (u v : F) : ProjectiveLine F → ProjectiveLine F
  | none => none
  | some (none, b) => some (none, b + u)
  | some (some a, b) => some (some a, b + v - a * u)

private theorem translatePointMap_left_inv (u v : F) :
    Function.LeftInverse (translatePointMap (-u) (-v)) (translatePointMap u v) := by
  rintro (⟨x, y⟩ | d) <;> simp [translatePointMap]

private theorem translateLineMap_left_inv (u v : F) :
    Function.LeftInverse (translateLineMap (-u) (-v)) (translateLineMap u v) := by
  intro l
  cases l with
  | none => rfl
  | some l =>
    rcases l with ⟨d, b⟩
    cases d with
    | none => simp [translateLineMap]
    | some slope => simp [translateLineMap]; ring

def translate (u v : F) : ProjectiveTransform F where
  points :=
    { toFun := translatePointMap u v
      invFun := translatePointMap (-u) (-v)
      left_inv := translatePointMap_left_inv u v
      right_inv := by
        intro p
        simpa only [neg_neg] using translatePointMap_left_inv (-u) (-v) p }
  lines :=
    { toFun := translateLineMap u v
      invFun := translateLineMap (-u) (-v)
      left_inv := translateLineMap_left_inv u v
      right_inv := by
        intro l
        simpa only [neg_neg] using translateLineMap_left_inv (-u) (-v) l }
  incidence := by
    intro p l
    change ProjectiveIncidence (translatePointMap u v p) (translateLineMap u v l) ↔
      ProjectiveIncidence p l
    cases p with
    | inl p =>
      rcases p with ⟨x, y⟩
      cases l with
      | none => rfl
      | some l =>
        rcases l with ⟨d, b⟩
        cases d with
        | none => simp [translatePointMap, translateLineMap, ProjectiveIncidence,
            Incidence, projection]
        | some a =>
          change y + v - a * (x + u) = b + v - a * u ↔ y - a * x = b
          have hleft : y + v - a * (x + u) = (y - a * x) + (v - a * u) := by ring
          have hright : b + v - a * u = b + (v - a * u) := by ring
          rw [hleft, hright]
          exact add_right_cancel_iff
    | inr d =>
      cases l with
      | none => rfl
      | some l =>
        rcases l with ⟨e, b⟩
        cases e <;> rfl

@[simp] theorem translate_points_finite (u v : F) (p : Point F) :
    (translate u v).points (Sum.inl p) = Sum.inl (p.1 + u, p.2 + v) := rfl

@[simp] theorem translate_points_infinite (u v : F) (d : Direction F) :
    (translate u v).points (Sum.inr d) = Sum.inr d := rfl

@[simp] theorem translate_lines_infinity (u v : F) :
    (translate u v).lines none = none := rfl

@[simp] theorem translate_lines_vertical (u v b : F) :
    (translate u v).lines (some (none, b)) = some (none, b + u) := rfl

@[simp] theorem translate_lines_slope (u v a b : F) :
    (translate u v).lines (some (some a, b)) = some (some a, b + v - a * u) := rfl

private def shearPointMap (r : F) : ProjectivePoint F → ProjectivePoint F
  | Sum.inl p => Sum.inl (p.1, p.2 + r * p.1)
  | Sum.inr none => Sum.inr none
  | Sum.inr (some a) => Sum.inr (some (a + r))

private def shearLineMap (r : F) : ProjectiveLine F → ProjectiveLine F
  | none => none
  | some (none, b) => some (none, b)
  | some (some a, b) => some (some (a + r), b)

private theorem shearPointMap_left_inv (r : F) :
    Function.LeftInverse (shearPointMap (-r)) (shearPointMap r) := by
  intro p
  cases p with
  | inl p => rcases p with ⟨x, y⟩; simp [shearPointMap]
  | inr d => cases d <;> simp [shearPointMap]

private theorem shearLineMap_left_inv (r : F) :
    Function.LeftInverse (shearLineMap (-r)) (shearLineMap r) := by
  intro l
  cases l with
  | none => rfl
  | some l =>
    rcases l with ⟨d, b⟩
    cases d <;> simp [shearLineMap]

def shear (r : F) : ProjectiveTransform F where
  points :=
    { toFun := shearPointMap r
      invFun := shearPointMap (-r)
      left_inv := shearPointMap_left_inv r
      right_inv := by
        intro p
        simpa only [neg_neg] using shearPointMap_left_inv (-r) p }
  lines :=
    { toFun := shearLineMap r
      invFun := shearLineMap (-r)
      left_inv := shearLineMap_left_inv r
      right_inv := by
        intro l
        simpa only [neg_neg] using shearLineMap_left_inv (-r) l }
  incidence := by
    intro p l
    change ProjectiveIncidence (shearPointMap r p) (shearLineMap r l) ↔
      ProjectiveIncidence p l
    cases p with
    | inl p =>
      rcases p with ⟨x, y⟩
      cases l with
      | none => rfl
      | some l =>
        rcases l with ⟨d, b⟩
        cases d with
        | none => rfl
        | some a =>
          change y + r * x - (a + r) * x = b ↔ y - a * x = b
          have h : y + r * x - (a + r) * x = y - a * x := by ring
          rw [h]
    | inr d =>
      cases l with
      | none => cases d <;> rfl
      | some l =>
        rcases l with ⟨e, b⟩
        cases d <;> cases e <;> simp [shearPointMap, shearLineMap, ProjectiveIncidence]

@[simp] theorem shear_points_finite (r : F) (p : Point F) :
    (shear r).points (Sum.inl p) = Sum.inl (p.1, p.2 + r * p.1) := rfl

@[simp] theorem shear_points_infinite_vertical (r : F) :
    (shear r).points (Sum.inr none) = Sum.inr none := rfl

@[simp] theorem shear_points_infinite_slope (r a : F) :
    (shear r).points (Sum.inr (some a)) = Sum.inr (some (a + r)) := rfl

@[simp] theorem shear_lines_infinity (r : F) :
    (shear r).lines none = none := rfl

@[simp] theorem shear_lines_vertical (r b : F) :
    (shear r).lines (some (none, b)) = some (none, b) := rfl

@[simp] theorem shear_lines_slope (r a b : F) :
    (shear r).lines (some (some a, b)) = some (some (a + r), b) := rfl

private def scaleYPointMap (c : F) : ProjectivePoint F → ProjectivePoint F
  | Sum.inl p => Sum.inl (p.1, c * p.2)
  | Sum.inr none => Sum.inr none
  | Sum.inr (some a) => Sum.inr (some (c * a))

private def scaleYLineMap (c : F) : ProjectiveLine F → ProjectiveLine F
  | none => none
  | some (none, b) => some (none, b)
  | some (some a, b) => some (some (c * a), c * b)

private theorem scaleYPointMap_left_inv (c : F) (hc : c ≠ 0) :
    Function.LeftInverse (scaleYPointMap c⁻¹) (scaleYPointMap c) := by
  intro p
  cases p with
  | inl p => rcases p with ⟨x, y⟩; simp [scaleYPointMap, hc]
  | inr d => cases d <;> simp [scaleYPointMap, hc]

private theorem scaleYLineMap_left_inv (c : F) (hc : c ≠ 0) :
    Function.LeftInverse (scaleYLineMap c⁻¹) (scaleYLineMap c) := by
  intro l
  cases l with
  | none => rfl
  | some l =>
    rcases l with ⟨d, b⟩
    cases d <;> simp [scaleYLineMap, hc]

def scaleY (c : F) (hc : c ≠ 0) : ProjectiveTransform F where
  points :=
    { toFun := scaleYPointMap c
      invFun := scaleYPointMap c⁻¹
      left_inv := scaleYPointMap_left_inv c hc
      right_inv := by
        intro p
        simpa only [inv_inv] using scaleYPointMap_left_inv c⁻¹ (inv_ne_zero hc) p }
  lines :=
    { toFun := scaleYLineMap c
      invFun := scaleYLineMap c⁻¹
      left_inv := scaleYLineMap_left_inv c hc
      right_inv := by
        intro l
        simpa only [inv_inv] using scaleYLineMap_left_inv c⁻¹ (inv_ne_zero hc) l }
  incidence := by
    intro p l
    change ProjectiveIncidence (scaleYPointMap c p) (scaleYLineMap c l) ↔
      ProjectiveIncidence p l
    cases p with
    | inl p =>
      rcases p with ⟨x, y⟩
      cases l with
      | none => rfl
      | some l =>
        rcases l with ⟨d, b⟩
        cases d with
        | none => rfl
        | some a =>
          change c * y - (c * a) * x = c * b ↔ y - a * x = b
          have h : c * y - (c * a) * x = c * (y - a * x) := by ring
          rw [h]
          exact mul_right_inj' hc
    | inr d =>
      cases l with
      | none => cases d <;> rfl
      | some l =>
        rcases l with ⟨e, b⟩
        cases d <;> cases e <;>
          simp [scaleYPointMap, scaleYLineMap, ProjectiveIncidence, mul_right_inj' hc]

@[simp] theorem scaleY_points_finite (c : F) (hc : c ≠ 0) (p : Point F) :
    (scaleY c hc).points (Sum.inl p) = Sum.inl (p.1, c * p.2) := rfl

@[simp] theorem scaleY_points_infinite_vertical (c : F) (hc : c ≠ 0) :
    (scaleY c hc).points (Sum.inr none) = Sum.inr none := rfl

@[simp] theorem scaleY_points_infinite_slope (c : F) (hc : c ≠ 0) (a : F) :
    (scaleY c hc).points (Sum.inr (some a)) = Sum.inr (some (c * a)) := rfl

@[simp] theorem scaleY_lines_infinity (c : F) (hc : c ≠ 0) :
    (scaleY c hc).lines none = none := rfl

@[simp] theorem scaleY_lines_vertical (c : F) (hc : c ≠ 0) (b : F) :
    (scaleY c hc).lines (some (none, b)) = some (none, b) := rfl

@[simp] theorem scaleY_lines_slope (c : F) (hc : c ≠ 0) (a b : F) :
    (scaleY c hc).lines (some (some a, b)) = some (some (c * a), c * b) := rfl

end RyserCoveringCounterexample

end OAI
