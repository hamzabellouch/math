import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicExpressions

namespace OAI

/-! Rational bounds for the finite gate expressions on a coordinate box.
The glue primitives have global bounds, even when their arguments move. -/

namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff BigOperators

def SmoothAtom.bound : SmoothAtom → ℚ
  | .glue k => k.factorial
  | .denom k => 9 ^ k

theorem SmoothAtom.bound_nonneg (a : SmoothAtom) : 0 ≤ a.bound := by
  cases a <;> simp only [bound] <;> positivity

theorem SmoothAtom.val_bound (a : SmoothAtom) (x : ℝ) :
    |a.profile.val x| ≤ (a.bound : ℝ) := by
  cases a with
  | glue k => simpa [profile, ProfileExpr.val, bound] using gluePower_bound k x
  | denom k => simpa [profile, ProfileExpr.val, bound] using denomPower_bound k x

namespace NonperiodicExpr

def bound (M : ℚ) : NonperiodicExpr → ℚ
  | .const r => |r|
  | .coord _ => |M|
  | .atom a _ => a.bound
  | .add e f => e.bound M + f.bound M
  | .mul e f => e.bound M * f.bound M

theorem bound_nonneg (e : NonperiodicExpr) (M : ℚ) : 0 ≤ e.bound M := by
  induction e with
  | const r => exact abs_nonneg _
  | coord j => exact abs_nonneg _
  | atom a e ih => exact a.bound_nonneg
  | add e f he hf => exact add_nonneg he hf
  | mul e f he hf => exact mul_nonneg he hf

theorem val_bound (e : NonperiodicExpr) (M : ℚ) (y : SpaceTime)
    (hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) : |e.val y| ≤ (e.bound M : ℝ) := by
  induction e with
  | const r => simp [val, bound]
  | coord j => simpa only [val, bound, Rat.cast_abs] using hy j
  | atom a e ih => exact a.val_bound _
  | add e f ihe ihf =>
    simpa only [val, bound, Rat.cast_add] using
      (abs_add_le _ _).trans (add_le_add ihe ihf)
  | mul e f ihe ihf =>
    simpa only [val, bound, Rat.cast_mul, abs_mul] using
      mul_le_mul ihe ihf (abs_nonneg _) (Rat.cast_nonneg.mpr (e.bound_nonneg M))

def derivativeBound (e : NonperiodicExpr) (M : ℚ) : ℚ :=
  ∑ j : Fin 4, (e.diff j).bound M

theorem derivativeBound_nonneg (e : NonperiodicExpr) (M : ℚ) :
    0 ≤ e.derivativeBound M := Finset.sum_nonneg (fun j _ => (e.diff j).bound_nonneg M)

theorem fderiv_bound (e : NonperiodicExpr) (M : ℚ) (y : SpaceTime)
    (hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) :
    ‖fderiv ℝ e.val y‖ ≤ (e.derivativeBound M : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Rat.cast_nonneg.mpr (e.derivativeBound_nonneg M))
  intro v
  conv_lhs => rw [← spaceTimeDirections_sum v]
  rw [map_sum]
  calc
    _ ≤ ∑ j : Fin 4, ‖fderiv ℝ e.val y (timeSpaceCoord j v • spaceTimeDirection j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin 4, ‖v‖ * ((e.diff j).bound M : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul]
      have hj : ‖fderiv ℝ e.val y (spaceTimeDirection j)‖ ≤ ((e.diff j).bound M : ℝ) := by
        rw [← e.val_diff j y, Real.norm_eq_abs]
        exact (e.diff j).val_bound M y hy
      exact mul_le_mul (timeSpaceCoord_norm j v) hj (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      rw [derivativeBound, Rat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem lipschitz_bound (e : NonperiodicExpr) (M : ℚ) (x y : SpaceTime)
    (hx : ∀ j, |timeSpaceCoord j x| ≤ |(M : ℝ)|)
    (hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) :
    |e.val x - e.val y| ≤ (e.derivativeBound M : ℝ) * ‖x - y‖ := by
  let S : Set SpaceTime := {z | ∀ j, |timeSpaceCoord j z| ≤ |(M : ℝ)|}
  have hc : Convex ℝ S := by
    intro u hu v hv a b ha hb hab j
    simp only [map_add, map_smul, smul_eq_mul]
    calc
      _ ≤ |a * timeSpaceCoord j u| + |b * timeSpaceCoord j v| := abs_add_le _ _
      _ = a * |timeSpaceCoord j u| + b * |timeSpaceCoord j v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * |(M : ℝ)| + b * |(M : ℝ)| := add_le_add
        (mul_le_mul_of_nonneg_left (hu j) ha) (mul_le_mul_of_nonneg_left (hv j) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => e.smooth.differentiable (by simp) z)
    (fun z hz => e.fderiv_bound M z hz) hc hy hx
  simpa only [Real.norm_eq_abs] using h

theorem mixed_bound (e : NonperiodicExpr) (α : List (Fin 4)) (M : ℚ) (y : SpaceTime)
    (hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) :
    |ClockedExpr.scalarMixed e.val α y| ≤ ((e.diffWord α).bound M : ℝ) := by
  rw [← e.val_diffWord α]
  exact (e.diffWord α).val_bound M y hy

end NonperiodicExpr
end ForcedComputation

end OAI
