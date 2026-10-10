import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedBounds

namespace OAI

/-! Finite smooth expressions for the moving whole-plane gates. Unlike
periodic field expressions, their profile arguments may depend on both
time and position. The only nonpolynomial primitives are the existing
effective flat glue and its everywhere positive transition denominator. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff

inductive SmoothAtom
  | glue (k : ℕ)
  | denom (k : ℕ)
  deriving DecidableEq

def SmoothAtom.profile : SmoothAtom → ProfileExpr
  | .glue k => .glue k 1 0
  | .denom k => .denom k 1 0

inductive NonperiodicExpr
  | const (r : ℚ)
  | coord (j : Fin 4)
  | atom (a : SmoothAtom) (e : NonperiodicExpr)
  | add (e f : NonperiodicExpr)
  | mul (e f : NonperiodicExpr)
  deriving DecidableEq

namespace NonperiodicExpr

noncomputable def val : NonperiodicExpr → SpaceTime → ℝ
  | .const r, _ => r
  | .coord j, y => timeSpaceCoord j y
  | .atom a e, y => a.profile.val (e.val y)
  | .add e f, y => e.val y + f.val y
  | .mul e f, y => e.val y * f.val y

def sub (e f : NonperiodicExpr) : NonperiodicExpr := .add e (.mul (.const (-1)) f)

def composeProfile : ProfileExpr → NonperiodicExpr → NonperiodicExpr
  | .const r, _ => .const r
  | .coord, e => e
  | .glue k a b, e => .atom (.glue k) (.add (.mul (.const a) e) (.const b))
  | .denom k a b, e => .atom (.denom k) (.add (.mul (.const a) e) (.const b))
  | .add p q, e => .add (composeProfile p e) (composeProfile q e)
  | .mul p q, e => .mul (composeProfile p e) (composeProfile q e)

theorem val_composeProfile (p : ProfileExpr) (e : NonperiodicExpr) (y : SpaceTime) :
    (composeProfile p e).val y = p.val (e.val y) := by
  induction p with
  | const => rfl
  | coord => rfl
  | glue k a b => simp [composeProfile, val, SmoothAtom.profile, ProfileExpr.val]
  | denom k a b => simp [composeProfile, val, SmoothAtom.profile, ProfileExpr.val]
  | add p q ihp ihq => exact congrArg₂ (· + ·) ihp ihq
  | mul p q ihp ihq => exact congrArg₂ (· * ·) ihp ihq

def diff (j : Fin 4) : NonperiodicExpr → NonperiodicExpr
  | .const _ => .const 0
  | .coord i => .const (if i = j then 1 else 0)
  | .atom a e => .mul (composeProfile a.profile.diff e) (e.diff j)
  | .add e f => .add (e.diff j) (f.diff j)
  | .mul e f => .add (.mul (e.diff j) f) (.mul e (f.diff j))

theorem smooth (e : NonperiodicExpr) : ContDiff ℝ ∞ e.val := by
  induction e with
  | const => exact contDiff_const
  | coord j => exact (timeSpaceCoord j).contDiff
  | atom a e ih => exact a.profile.smooth.comp ih
  | add e f ihe ihf => exact ihe.add ihf
  | mul e f ihe ihf => exact ihe.mul ihf

theorem val_diff (e : NonperiodicExpr) (j : Fin 4) (y : SpaceTime) :
    (e.diff j).val y = fderiv ℝ e.val y (spaceTimeDirection j) := by
  induction e with
  | const r => simp [diff, val]
  | coord i =>
    change ((if i = j then 1 else 0 : ℚ) : ℝ) =
      fderiv ℝ (timeSpaceCoord i) y (spaceTimeDirection j)
    rw [(timeSpaceCoord i).fderiv, timeSpaceCoord_direction]
    split_ifs <;> norm_num
  | atom a e ih =>
    have hd := (a.profile.hasDerivAt (e.val y)).comp_hasFDerivAt y
      ((smooth e).differentiable (by simp) y).hasFDerivAt
    change _ = fderiv ℝ (a.profile.val ∘ e.val) y (spaceTimeDirection j)
    rw [hd.fderiv]
    change (composeProfile a.profile.diff e).val y * (e.diff j).val y = _
    rw [val_composeProfile, ih]
    rfl
  | add e f ihe ihf =>
    rw [show NonperiodicExpr.val (.add e f) = e.val + f.val from rfl,
      fderiv_add ((smooth e).differentiable (by simp) y)
        ((smooth f).differentiable (by simp) y)]
    exact congrArg₂ (· + ·) ihe ihf
  | mul e f ihe ihf =>
    have hd := ((smooth e).differentiable (by simp) y).hasFDerivAt.mul
      ((smooth f).differentiable (by simp) y).hasFDerivAt
    change _ = fderiv ℝ (e.val * f.val) y (spaceTimeDirection j)
    rw [hd.fderiv]
    simp only [diff, val, add_apply, smul_apply, smul_eq_mul]
    rw [ihe, ihf]
    ring

def diffWord (e : NonperiodicExpr) : List (Fin 4) → NonperiodicExpr
  | [] => e
  | j :: α => (e.diffWord α).diff j

theorem val_diffWord (e : NonperiodicExpr) (α : List (Fin 4)) :
    (e.diffWord α).val = ClockedExpr.scalarMixed e.val α := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    change ((e.diffWord α).diff j).val y = _
    rw [val_diff, ih]
    rfl

end NonperiodicExpr
end ForcedComputation

end OAI
