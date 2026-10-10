import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicVector
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ResidualExpressions

namespace OAI

/-! Moving-gate syntax is closed under the full viscous residual. -/

namespace ForcedComputation
open ShearFlows
open scoped BigOperators

namespace NonperiodicExpr

def sum (l : List NonperiodicExpr) : NonperiodicExpr := l.foldr .add (.const 0)

theorem sum_val (l : List NonperiodicExpr) (y : SpaceTime) :
    (sum l).val y = (l.map (fun e => e.val y)).sum := by
  induction l with
  | nil => simp only [sum, List.foldr_nil, val, List.map_nil, List.sum_nil, Rat.cast_zero]
  | cons e l ih =>
    change e.val y + (sum l).val y = _
    simp only [List.map_cons, List.sum_cons, ih]

theorem sum_ofFn_val {n : ℕ} (e : Fin n → NonperiodicExpr) (y : SpaceTime) :
    (sum (List.ofFn e)).val y = ∑ j, (e j).val y := by
  rw [sum_val, List.map_ofFn, List.sum_ofFn]
  rfl

end NonperiodicExpr

namespace NonperiodicResidual

def convection (c : NonperiodicVector) : NonperiodicVector := fun k =>
  NonperiodicExpr.sum (List.ofFn (fun j : Fin 3 => .mul (c j) ((c k).diff j.succ)))

def linear (c : NonperiodicVector) (r : ℚ) : NonperiodicVector := fun k =>
  .add ((c k).diff 0) (.mul (.const (-r))
    (NonperiodicExpr.sum (List.ofFn (fun j : Fin 3 => (c k).diffWord [j.succ, j.succ]))))

def code (c : NonperiodicVector) (r : ℚ) : NonperiodicVector := fun k =>
  .add (linear c r k) (convection c k)

theorem convection_val (c : NonperiodicVector) :
    (convection c).val = convectiveField c.val := by
  funext y k
  rw [convectiveField_eq_mixed c.smooth]
  simp only [convection, NonperiodicVector.val, NonperiodicExpr.sum_ofFn_val,
    NonperiodicExpr.val, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrFun (congrFun (c.val_diffWord [j.succ]) y) k
  exact congrArg (fun z => (c j).val y * z) he

theorem linear_val (c : NonperiodicVector) (r : ℚ) :
    (linear c r).val = force r c.val := by
  funext y k
  rw [force_eq_mixed c.smooth]
  simp_rw [← c.val_diffWord]
  simp only [linear, NonperiodicVector.val, NonperiodicExpr.val, NonperiodicExpr.sum_ofFn_val,
    NonperiodicVector.diffWord, NonperiodicExpr.diffWord, Finset.sum_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_neg]
  ring

theorem val (c : NonperiodicVector) (r : ℚ) : (code c r).val = residual r c.val := by
  rw [residual_eq_force_add, ← linear_val c r, ← convection_val c]
  rfl

end NonperiodicResidual
end ForcedComputation

end OAI
