import OAI.NumberTheory.Ostmann.Arithmetic.MovingCellGap

namespace OAI

/-! # The backwards compensation-center construction of equation (7.4) -/

namespace Ostmann

/-- The entries are ordered from the first removed type to the last. -/
noncomputable def movingCompensationTargets (J : ℝ) : List ℝ → List ℝ
  | [] => []
  | d :: ds =>
    let rest := movingCompensationTargets J ds
    (J + rest.sum - d) :: rest

noncomputable def movingCompensationTargetError : List ℝ → ℝ
  | [] => 0
  | d :: ds => 2 * movingCompensationTargetError ds + d

@[simp] theorem movingCompensationTargets_length (J : ℝ) (ds : List ℝ) :
    (movingCompensationTargets J ds).length = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [movingCompensationTargets, List.length_cons, ih]

theorem movingCompensationTargets_sum (J : ℝ) (ds : List ℝ) :
    J + (movingCompensationTargets J ds).sum =
      (2 : ℝ) ^ ds.length * J - movingCompensationTargetError ds := by
  induction ds with
  | nil => simp only [movingCompensationTargets, List.sum_nil, List.length_nil,
      pow_zero, one_mul, movingCompensationTargetError, sub_zero, add_zero]
  | cons d ds ih =>
    simp only [movingCompensationTargets, List.sum_cons, List.length_cons,
      movingCompensationTargetError, pow_succ]
    linarith

theorem movingCompensationTargets_first (J d : ℝ) (ds : List ℝ) :
    movingCompensationTargets J (d :: ds) =
      ((2 : ℝ) ^ ds.length * J - movingCompensationTargetError ds - d) ::
        movingCompensationTargets J ds := by
  simp only [movingCompensationTargets, movingCompensationTargets_sum]

theorem movingCompensationTargetError_bounds (B : ℝ) (ds : List ℝ)
    (h : ∀ d ∈ ds, 0 ≤ d ∧ d ≤ B) :
    0 ≤ movingCompensationTargetError ds ∧
      movingCompensationTargetError ds ≤ ((2 : ℝ) ^ ds.length - 1) * B := by
  induction ds with
  | nil => simp only [movingCompensationTargetError, List.length_nil, pow_zero,
      sub_self, zero_mul, le_refl, and_self]
  | cons d ds ih =>
    have hd := h d (by simp)
    have ht := ih (fun x hx => h x (by simp only [List.mem_cons]; exact Or.inr hx))
    simp only [movingCompensationTargetError, List.length_cons, pow_succ]
    constructor <;> linarith

theorem movingCompensationTargets_first_error (J d B : ℝ) (ds : List ℝ)
    (h : ∀ e ∈ d :: ds, 0 ≤ e ∧ e ≤ B) :
    |(J + (movingCompensationTargets J ds).sum - d) - (2 : ℝ) ^ ds.length * J| ≤
      (2 : ℝ) ^ ds.length * B := by
  have hd := h d (by simp)
  have ht := movingCompensationTargetError_bounds B ds
    (fun x hx => h x (by simp only [List.mem_cons]; exact Or.inr hx))
  have hs := movingCompensationTargets_sum J ds
  rw [abs_of_nonpos (by linarith :
    J + (movingCompensationTargets J ds).sum - d - 2 ^ ds.length * J ≤ 0)]
  linarith

theorem movingCompensationTargets_balance (J gap r : ℝ) (hr : r ≠ 0) (ds : List ℝ) :
    r * (J + (movingCompensationTargets J ds).sum - gap / r) =
      r * (J + (movingCompensationTargets J ds).sum) - gap := by
  field_simp

end Ostmann

end OAI
