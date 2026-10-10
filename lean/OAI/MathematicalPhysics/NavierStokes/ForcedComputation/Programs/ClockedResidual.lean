import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedVector
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ResidualExpressions

namespace OAI

/-! Finite clocked expressions are closed under the full Navier–Stokes
residual, including the quadratic convection term. -/

namespace ForcedComputation
open ShearFlows
open scoped BigOperators

namespace ClockedExpr

def sum (l : List ClockedExpr) : ClockedExpr := l.foldr .add (.const 0)

theorem sum_valid {l : List ClockedExpr} (hl : ∀ e ∈ l, e.Valid) : (sum l).Valid := by
  induction l with
  | nil => trivial
  | cons e l ih =>
    exact ⟨hl e (by simp), ih (fun f hf => hl f (by simp [hf]))⟩

theorem sum_val (l : List ClockedExpr) (y : SpaceTime) :
    (sum l).val y = (l.map (fun e => e.val y)).sum := by
  induction l with
  | nil => simp only [sum, List.foldr_nil, val, List.map_nil, List.sum_nil, Rat.cast_zero]
  | cons e l ih =>
    change e.val y + (sum l).val y = _
    simp only [List.map_cons, List.sum_cons, ih]

theorem sum_ofFn_valid {n : ℕ} (e : Fin n → ClockedExpr) (he : ∀ j, (e j).Valid) :
    (sum (List.ofFn e)).Valid :=
  sum_valid (fun f hf => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf; exact he j)

theorem sum_ofFn_val {n : ℕ} (e : Fin n → ClockedExpr) (y : SpaceTime) :
    (sum (List.ofFn e)).val y = ∑ j, (e j).val y := by
  rw [sum_val, List.map_ofFn, List.sum_ofFn]
  rfl

end ClockedExpr

namespace ClockedResidual

def convection (c : ClockedVector) : ClockedVector := fun k =>
  ClockedExpr.sum (List.ofFn (fun j : Fin 3 => .mul (c j) ((c k).diff j.succ)))

def linear (c : ClockedVector) (r : ℚ) : ClockedVector := fun k =>
  .add ((c k).diff 0) (.mul (.const (-r))
    (ClockedExpr.sum (List.ofFn (fun j : Fin 3 => (c k).diffWord [j.succ, j.succ]))))

def code (c : ClockedVector) (r : ℚ) : ClockedVector := fun k =>
  .add (linear c r k) (convection c k)

theorem convection_valid {c : ClockedVector} (hc : c.Valid) : (convection c).Valid := by
  intro k
  exact ClockedExpr.sum_ofFn_valid _ (fun j => ⟨hc j, (c k).valid_diff (hc k) j.succ⟩)

theorem linear_valid {c : ClockedVector} (hc : c.Valid) (r : ℚ) :
    (linear c r).Valid := by
  intro k
  exact ⟨(c k).valid_diff (hc k) 0, trivial,
    ClockedExpr.sum_ofFn_valid _ (fun j => (c k).valid_diffWord (hc k) _)⟩

theorem valid {c : ClockedVector} (hc : c.Valid) (r : ℚ) : (code c r).Valid :=
  fun k => ⟨linear_valid hc r k, convection_valid hc k⟩

theorem convection_val {c : ClockedVector} (hc : c.Valid) :
    (convection c).val = convectiveField c.val := by
  funext y k
  rw [convectiveField_eq_mixed (ClockedVector.smooth hc)]
  simp only [convection, ClockedVector.val, ClockedExpr.sum_ofFn_val,
    ClockedExpr.val, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrFun (congrFun (ClockedVector.val_diffWord hc [j.succ]) y) k
  exact congrArg (fun z => (c j).val y * z) he

theorem linear_val {c : ClockedVector} (hc : c.Valid) (r : ℚ) :
    (linear c r).val = force r c.val := by
  funext y k
  rw [force_eq_mixed (ClockedVector.smooth hc)]
  simp_rw [← ClockedVector.val_diffWord hc]
  simp only [linear, ClockedVector.val, ClockedExpr.val, ClockedExpr.sum_ofFn_val,
    ClockedVector.diffWord, ClockedExpr.diffWord, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Rat.cast_neg]
  ring

theorem val {c : ClockedVector} (hc : c.Valid) (r : ℚ) :
    (code c r).val = residual r c.val := by
  rw [residual_eq_force_add, ← linear_val hc r, ← convection_val hc]
  rfl

end ClockedResidual
end ForcedComputation

end OAI
