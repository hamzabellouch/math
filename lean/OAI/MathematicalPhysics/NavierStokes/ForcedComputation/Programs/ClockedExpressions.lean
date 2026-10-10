import OAI.MathematicalPhysics.NavierStokes.ShearFlows.FieldExpressions

namespace OAI

/-! Finite expressions for the prescribed detector clock. Differentiation
keeps the smooth clock separate from the periodic field it samples. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff

noncomputable def clockedPoint (q : ProfileExpr) (y : SpaceTime) : SpaceTime :=
  (q.val y.1, y.2)

theorem clockedPoint_smooth (q : ProfileExpr) : ContDiff ℝ ∞ (clockedPoint q) :=
  (q.smooth.comp contDiff_fst).prodMk contDiff_snd

theorem clockedPoint_direction (q : ProfileExpr) (y : SpaceTime) (j : Fin 4) :
    fderiv ℝ (clockedPoint q) y (spaceTimeDirection j) =
      if j = 0 then q.diff.val y.1 • spaceTimeDirection 0 else spaceTimeDirection j := by
  have hq := (q.hasDerivAt y.1).comp_hasFDerivAt y
    (ContinuousLinearMap.fst ℝ ℝ Space).hasFDerivAt
  have hd := hq.prodMk (ContinuousLinearMap.snd ℝ ℝ Space).hasFDerivAt
  change HasFDerivAt (clockedPoint q) _ y at hd
  rw [hd.fderiv]
  cases j using Fin.cases with
  | zero => simp [spaceTimeDirection, Prod.smul_mk]
  | succ k => simp [spaceTimeDirection]

inductive ClockedExpr
  | const (r : ℚ)
  | profile (q : ProfileExpr)
  | field (q : ProfileExpr) (e : FieldExpr)
  | add (e f : ClockedExpr)
  | mul (e f : ClockedExpr)
  deriving DecidableEq

namespace ClockedExpr

noncomputable def val : ClockedExpr → SpaceTime → ℝ
  | .const r, _ => r
  | .profile q, y => q.val y.1
  | .field q e, y => e.val (clockedPoint q y)
  | .add e f, y => e.val y + f.val y
  | .mul e f, y => e.val y * f.val y

def Valid : ClockedExpr → Prop
  | .const _ => True
  | .profile _ => True
  | .field _ e => e.Valid
  | .add e f => e.Valid ∧ f.Valid
  | .mul e f => e.Valid ∧ f.Valid

def diff (j : Fin 4) : ClockedExpr → ClockedExpr
  | .const _ => .const 0
  | .profile q => if j = 0 then .profile q.diff else .const 0
  | .field q e => if j = 0 then .mul (.profile q.diff) (.field q (e.diff 0))
      else .field q (e.diff j)
  | .add e f => .add (e.diff j) (f.diff j)
  | .mul e f => .add (.mul (e.diff j) f) (.mul e (f.diff j))

theorem valid_diff {e : ClockedExpr} (he : e.Valid) (j : Fin 4) : (e.diff j).Valid := by
  induction e with
  | const => trivial
  | profile => simp only [diff]; split_ifs <;> trivial
  | field q e =>
    by_cases hj : j = 0
    · simp only [diff, hj, ite_true, Valid]
      exact ⟨trivial, e.valid_diff he 0⟩
    · simpa only [diff, hj, ite_false, Valid] using e.valid_diff he j
  | add e f ih₁ ih₂ => exact ⟨ih₁ he.1, ih₂ he.2⟩
  | mul e f ih₁ ih₂ => exact ⟨⟨ih₁ he.1, he.2⟩, ⟨he.1, ih₂ he.2⟩⟩

theorem smooth {e : ClockedExpr} (he : e.Valid) : ContDiff ℝ ∞ e.val := by
  induction e with
  | const => exact contDiff_const
  | profile q => exact q.smooth.comp contDiff_fst
  | field q e => exact (e.smooth he).comp (clockedPoint_smooth q)
  | add e f ih₁ ih₂ => exact (ih₁ he.1).add (ih₂ he.2)
  | mul e f ih₁ ih₂ => exact (ih₁ he.1).mul (ih₂ he.2)

theorem val_diff {e : ClockedExpr} (he : e.Valid) (j : Fin 4) (y : SpaceTime) :
    (e.diff j).val y = fderiv ℝ e.val y (spaceTimeDirection j) := by
  induction e with
  | const r => simp [diff, val]
  | profile q =>
    have hd := (q.hasDerivAt y.1).comp_hasFDerivAt y
      (ContinuousLinearMap.fst ℝ ℝ Space).hasFDerivAt
    change _ = fderiv ℝ (q.val ∘ Prod.fst) y (spaceTimeDirection j)
    rw [hd.fderiv]
    cases j using Fin.cases with
    | zero => simp [diff, val, spaceTimeDirection]
    | succ k => simp [diff, val, spaceTimeDirection]
  | field q e =>
    have hd := ((e.smooth he).differentiable (by simp) (clockedPoint q y)).hasFDerivAt.comp y
      ((clockedPoint_smooth q).differentiable (by simp) y).hasFDerivAt
    change _ = fderiv ℝ (e.val ∘ clockedPoint q) y (spaceTimeDirection j)
    rw [hd.fderiv, ContinuousLinearMap.comp_apply, clockedPoint_direction]
    by_cases hj : j = 0
    · subst j
      simp only [diff, ite_true, val, map_smul, smul_eq_mul]
      rw [e.val_diff he 0]
    · simp only [diff, hj, ite_false, val]
      exact e.val_diff he j _
  | add e f ih₁ ih₂ =>
    rw [show ClockedExpr.val (.add e f) = e.val + f.val from rfl,
      fderiv_add ((smooth he.1).differentiable (by simp) y)
        ((smooth he.2).differentiable (by simp) y)]
    exact congrArg₂ (· + ·) (ih₁ he.1) (ih₂ he.2)
  | mul e f ih₁ ih₂ =>
    have hd := ((smooth he.1).differentiable (by simp) y).hasFDerivAt.mul
      ((smooth he.2).differentiable (by simp) y).hasFDerivAt
    change _ = fderiv ℝ (e.val * f.val) y (spaceTimeDirection j)
    rw [hd.fderiv]
    simp only [diff, val, add_apply, smul_apply, smul_eq_mul]
    rw [ih₁ he.1, ih₂ he.2]
    ring

end ClockedExpr
end ForcedComputation

end OAI
