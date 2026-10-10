import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ResidualScaling
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceEvaluation

namespace OAI

/-! Finite expressions and certified evaluation for the full viscous residual,
including the quadratic convection term. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff BigOperators

theorem mixedDerivative_add {V W : Velocity} (hV : ContDiff ℝ ∞ V)
    (hW : ContDiff ℝ ∞ W) (α : List (Fin 4)) :
    mixedDerivative (V + W) α = mixedDerivative V α + mixedDerivative W α := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    simp only [mixedDerivative, ih]
    rw [fderiv_add ((mixedDerivative_smooth hV α).differentiable (by simp) y)
      ((mixedDerivative_smooth hW α).differentiable (by simp) y)]
    rfl

noncomputable def convectiveField (V : Velocity) : Velocity :=
  fun y => advection (fun x => V (y.1, x)) y.2

theorem convectiveField_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (convectiveField V) :=
  (spatial_fderiv_smooth hV).clm_apply hV

theorem convectiveField_eq_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (y : SpaceTime) :
    convectiveField V y = ∑ j : Fin 3, V y j • mixedDerivative V [j.succ] y := by
  change fderiv ℝ (fun x => V (y.1, x)) y.2 (V y) = _
  calc
    _ = fderiv ℝ (fun x => V (y.1, x)) y.2
        (∑ j : Fin 3, V y j • basis j) := by rw [sum_coordinates_basis]
    _ = ∑ j : Fin 3, V y j • derivative (fun x => V (y.1, x)) j y.2 := by
      simp only [map_sum, map_smul, derivative]
    _ = _ := by simp only [spatialDerivative_eq_mixed hV]

theorem residual_eq_force_add (ν : ℝ) (V : Velocity) :
    residual ν V = force ν V + convectiveField V := by
  funext y
  simp only [residual, force, convectiveField, Pi.add_apply]
  abel

namespace ResidualCode

def convection (c : VelocityExpr) : VelocityExpr := fun k =>
  FieldExpr.sum (List.ofFn (fun j : Fin 3 => .mul (c j) ((c k).diff j.succ)))

theorem convection_valid {c : VelocityExpr} (hc : c.Valid) : (convection c).Valid := by
  intro k
  exact FieldExpr.sum_ofFn_valid _ (fun j => ⟨hc j, FieldExpr.valid_diff (hc k) j.succ⟩)

theorem convection_val {c : VelocityExpr} (hc : c.Valid) :
    (convection c).val = convectiveField c.val := by
  funext y k
  rw [convectiveField_eq_mixed (VelocityExpr.smooth hc)]
  simp only [convection, VelocityExpr.val, FieldExpr.sum_ofFn_val,
    FieldExpr.val, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrFun (congrFun (VelocityExpr.val_diffWord hc [j.succ]) y) k
  exact congrArg (fun z => (c j).val y * z) he

def code (c : VelocityExpr) (r : ℚ) : VelocityExpr := fun k =>
  .add (c.forceCode r k) (convection c k)

theorem valid {c : VelocityExpr} (hc : c.Valid) (r : ℚ) : (code c r).Valid :=
  fun k => ⟨VelocityExpr.forceCode_valid hc r k, convection_valid hc k⟩

theorem val {c : VelocityExpr} (hc : c.Valid) (r : ℚ) :
    (code c r).val = residual r c.val := by
  rw [residual_eq_force_add, ← VelocityExpr.forceCode_val hc r, ← convection_val hc]
  rfl

theorem coefficient_error {c : VelocityExpr} (hc : c.Valid)
    (α : List (Fin 4)) (y : SpaceTime) (ν r : ℝ) :
    ‖mixedDerivative (residual ν c.val) α y -
      mixedDerivative (residual r c.val) α y‖ ≤
      |ν-r| * (c.laplaceBound α : ℝ) := by
  rw [residual_eq_force_add, residual_eq_force_add,
    mixedDerivative_add (force_smooth (VelocityExpr.smooth hc) ν)
      (convectiveField_smooth (VelocityExpr.smooth hc)),
    mixedDerivative_add (force_smooth (VelocityExpr.smooth hc) r)
      (convectiveField_smooth (VelocityExpr.smooth hc))]
  simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using
    VelocityExpr.force_coefficient_error hc α y ν r

theorem halfTolerance_pos (ε : ℚ) (hε : 0 < ε) : 0 < ε/2 := half_pos hε

def evaluate (c : VelocityExpr) (hc : c.Valid) (α : List (Fin 4))
    (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  let r := a (c.coefficientPrecision α ε)
  (code c r).evaluate (valid hc r) α b (ε/2) (halfTolerance_pos ε hε)

theorem evaluate_spec {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4))
    {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    {y : SpaceTime} {b : ℕ → RationalSpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (residual ν c.val) α y -
      rationalVector (evaluate c hc α a b ε hε)‖ ≤ (ε : ℝ) := by
  let r := a (c.coefficientPrecision α ε)
  calc
    _ ≤ ‖mixedDerivative (residual ν c.val) α y - mixedDerivative (residual r c.val) α y‖ +
        ‖mixedDerivative (residual r c.val) α y -
          rationalVector (evaluate c hc α a b ε hε)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (ε : ℝ)/2 + (ε : ℝ)/2 := by
      apply add_le_add
      · exact (coefficient_error hc α y ν r).trans
          ((mul_le_mul_of_nonneg_right (ha _) (Nat.cast_nonneg _)).trans
            (VelocityExpr.coefficientPrecision_spec c α hε))
      · simpa only [evaluate, val hc, Rat.cast_div, Rat.cast_ofNat] using
          VelocityExpr.evaluate_spec (valid hc r) α b hb (ε/2) (by positivity)
    _ = _ := by ring

def bound (c : VelocityExpr) (α : List (Fin 4)) (a : ℕ → ℚ) : ℕ :=
  ⌈((code c 0).bound α : ℚ) + (|a 0|+1) * (c.laplaceBound α : ℚ)⌉₊

theorem bound_spec {c : VelocityExpr} (hc : c.Valid) (α : List (Fin 4))
    {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν) (y : SpaceTime) :
    ‖mixedDerivative (residual ν c.val) α y‖ ≤ (bound c α a : ℝ) := by
  have hν : |ν| ≤ |(a 0 : ℝ)|+1 := by
    have hh := ha 0
    simp only [errorTolerance, pow_zero, inv_one] at hh
    linarith [abs_sub_abs_le_abs_sub ν (a 0)]
  calc
    _ ≤ ‖mixedDerivative (residual 0 c.val) α y‖ +
        ‖mixedDerivative (residual ν c.val) α y - mixedDerivative (residual 0 c.val) α y‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub
        (mixedDerivative (residual 0 c.val) α y) (mixedDerivative (residual ν c.val) α y)
    _ ≤ ((code c 0).bound α : ℝ) + (|(a 0 : ℝ)|+1) * (c.laplaceBound α : ℝ) := by
      apply add_le_add
      · simpa only [val hc, Rat.cast_zero] using VelocityExpr.val_bound (valid hc 0) α y
      · exact (coefficient_error hc α y ν 0).trans
          (by simpa only [sub_zero] using
            mul_le_mul_of_nonneg_right hν (Nat.cast_nonneg (c.laplaceBound α)))
    _ ≤ _ := by exact_mod_cast (Nat.le_ceil
        (((code c 0).bound α : ℚ) + (|a 0|+1) * (c.laplaceBound α : ℚ)))

end ResidualCode
end ForcedComputation

end OAI
