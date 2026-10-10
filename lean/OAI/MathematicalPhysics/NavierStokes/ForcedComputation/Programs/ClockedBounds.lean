import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedExpressions
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EffectiveInterface

namespace OAI

/-! Local effective bounds for clocked expressions. Periodic field factors
have global bounds; only the explicit clock profiles use a time radius. -/

namespace ForcedComputation.ClockedExpr
open ShearFlows
open scoped ContDiff BigOperators

def bound (M : ℚ) : ClockedExpr → ℚ
  | .const r => |r|
  | .profile q => q.bound M
  | .field _ e => e.bound
  | .add e f => e.bound M + f.bound M
  | .mul e f => e.bound M * f.bound M

theorem bound_nonneg (e : ClockedExpr) (M : ℚ) : 0 ≤ e.bound M := by
  induction e with
  | const => exact abs_nonneg _
  | profile q => exact q.bound_nonneg M
  | field q e => exact e.bound_nonneg
  | add e f he hf => exact add_nonneg he hf
  | mul e f he hf => exact mul_nonneg he hf

theorem val_bound {e : ClockedExpr} (he : e.Valid) (M : ℚ) (y : SpaceTime)
    (hy : |y.1| ≤ |(M : ℝ)|) : |e.val y| ≤ (e.bound M : ℝ) := by
  induction e with
  | const r => simp [val, bound]
  | profile q => exact q.val_bound hy
  | field q e => exact e.val_bound he _
  | add e f ih₁ ih₂ =>
    simpa only [val, bound, Rat.cast_add] using
      (abs_add_le _ _).trans (add_le_add (ih₁ he.1) (ih₂ he.2))
  | mul e f ih₁ ih₂ =>
    simpa only [val, bound, Rat.cast_mul, abs_mul] using
      mul_le_mul (ih₁ he.1) (ih₂ he.2) (abs_nonneg _)
        (Rat.cast_nonneg.mpr (e.bound_nonneg M))

def diffWord (e : ClockedExpr) : List (Fin 4) → ClockedExpr
  | [] => e
  | j :: α => (e.diffWord α).diff j

theorem valid_diffWord {e : ClockedExpr} (he : e.Valid) (α : List (Fin 4)) :
    (e.diffWord α).Valid := by
  induction α with
  | nil => exact he
  | cons j α ih => exact valid_diff ih j

noncomputable def scalarMixed (f : SpaceTime → ℝ) : List (Fin 4) → SpaceTime → ℝ :=
  List.rec f (fun j _ g y => fderiv ℝ g y (spaceTimeDirection j))

theorem val_diffWord {e : ClockedExpr} (he : e.Valid) (α : List (Fin 4)) :
    (e.diffWord α).val = scalarMixed e.val α := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    change ((e.diffWord α).diff j).val y = _
    rw [val_diff (valid_diffWord he α), ih]
    rfl

theorem mixed_bound {e : ClockedExpr} (he : e.Valid) (α : List (Fin 4))
    (M : ℚ) (y : SpaceTime) (hy : |y.1| ≤ |(M : ℝ)|) :
    |scalarMixed e.val α y| ≤ ((e.diffWord α).bound M : ℝ) := by
  rw [← val_diffWord he α]
  exact val_bound (valid_diffWord he α) M y hy

end ForcedComputation.ClockedExpr

end OAI
