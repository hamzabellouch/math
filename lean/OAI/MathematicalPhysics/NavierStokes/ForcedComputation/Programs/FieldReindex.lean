import OAI.MathematicalPhysics.NavierStokes.ShearFlows.FieldExpressions

namespace OAI

/-! Coordinate changes in finite field expressions. This moves the planar
processor's periodic phase from its third spatial coordinate to time. -/

namespace ForcedComputation
open ShearFlows

noncomputable def reindexPoint (σ : Fin 4 → Fin 4) (y : SpaceTime) : SpaceTime :=
  (timeSpaceCoord (σ 0) y, fun j => timeSpaceCoord (σ j.succ) y)

theorem timeSpaceCoord_reindex (σ : Fin 4 → Fin 4) (j : Fin 4) (y : SpaceTime) :
    timeSpaceCoord j (reindexPoint σ y) = timeSpaceCoord (σ j) y := by
  fin_cases j <;> rfl

def _root_.OAI.ShearFlows.FieldExpr.reindex (σ : Fin 4 → Fin 4) : FieldExpr → FieldExpr
  | .const r => .const r
  | .atom j p => .atom (σ j) p
  | .add e f => .add (e.reindex σ) (f.reindex σ)
  | .mul e f => .mul (e.reindex σ) (f.reindex σ)

theorem _root_.OAI.ShearFlows.FieldExpr.valid_reindex {e : FieldExpr} (he : e.Valid) (σ : Fin 4 → Fin 4) :
    (e.reindex σ).Valid := by
  induction e with
  | const => trivial
  | atom j p => exact he
  | add e f ih₁ ih₂ => exact ⟨ih₁ he.1, ih₂ he.2⟩
  | mul e f ih₁ ih₂ => exact ⟨ih₁ he.1, ih₂ he.2⟩

theorem _root_.OAI.ShearFlows.FieldExpr.val_reindex (e : FieldExpr) (σ : Fin 4 → Fin 4) (y : SpaceTime) :
    (e.reindex σ).val y = e.val (reindexPoint σ y) := by
  induction e with
  | const => rfl
  | atom j p => simp only [FieldExpr.reindex, FieldExpr.val, timeSpaceCoord_reindex]
  | add e f ih₁ ih₂ => simp only [FieldExpr.reindex, FieldExpr.val, ih₁, ih₂]
  | mul e f ih₁ ih₂ => simp only [FieldExpr.reindex, FieldExpr.val, ih₁, ih₂]

def timeHeightSwap : Fin 4 → Fin 4 := ![3, 1, 2, 0]

theorem reindexPoint_timeHeightSwap (y : SpaceTime) :
    reindexPoint timeHeightSwap y = (y.2 2, atHeight (horizontal y.2) y.1) := by
  apply Prod.ext
  · rfl
  · ext j
    fin_cases j <;> rfl

theorem _root_.OAI.ShearFlows.FieldExpr.val_timeHeightSwap (e : FieldExpr) (y : SpaceTime) :
    (e.reindex timeHeightSwap).val y = e.val (y.2 2, atHeight (horizontal y.2) y.1) := by
  rw [FieldExpr.val_reindex, reindexPoint_timeHeightSwap]

end ForcedComputation

end OAI
