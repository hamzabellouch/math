import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicEvaluation

namespace OAI

/-! Three-component moving-gate programs and their certified mixed jets. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped ContDiff BigOperators

abbrev NonperiodicVector := Fin 3 → NonperiodicExpr

namespace NonperiodicVector

def val (c : NonperiodicVector) : Velocity := fun y j => (c j).val y

def diffWord (c : NonperiodicVector) (α : List (Fin 4)) : NonperiodicVector :=
  fun j => (c j).diffWord α

theorem smooth (c : NonperiodicVector) : ContDiff ℝ ∞ c.val :=
  contDiff_pi.mpr (fun j => (c j).smooth)

theorem val_diffWord (c : NonperiodicVector) (α : List (Fin 4)) :
    (c.diffWord α).val = mixedDerivative c.val α := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext y j
    rw [mixedDerivative, ← ih]
    have h := fderiv_pi (fun k => (((c k).diffWord α).smooth).differentiable (by simp) y)
    change ((c j).diffWord (i :: α)).val y =
      (fderiv ℝ (c.diffWord α).val y (spaceTimeDirection i)) j
    change fderiv ℝ (c.diffWord α).val y = _ at h
    rw [h]
    exact ((c j).diffWord α).val_diff i y

def bound (c : NonperiodicVector) (α : List (Fin 4)) (M : ℚ) : ℚ :=
  ∑ j, ((c j).diffWord α).bound M

theorem bound_nonneg (c : NonperiodicVector) (α : List (Fin 4)) (M : ℚ) :
    0 ≤ c.bound α M := Finset.sum_nonneg (fun j _ => ((c j).diffWord α).bound_nonneg M)

theorem val_bound (c : NonperiodicVector) (α : List (Fin 4)) (M : ℚ) (y : SpaceTime)
    (hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) :
    ‖mixedDerivative c.val α y‖ ≤ (c.bound α M : ℝ) := by
  rw [← c.val_diffWord α]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr (c.bound_nonneg α M))).mpr
  intro j
  apply (((c j).diffWord α).val_bound M y hy).trans
  exact_mod_cast Finset.single_le_sum
    (fun k _ => ((c k).diffWord α).bound_nonneg M) (Finset.mem_univ j)

def evaluate (c : NonperiodicVector) (α : List (Fin 4))
    (a : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  fun j => ((c j).diffWord α).evaluate a ε hε

theorem evaluate_spec (c : NonperiodicVector) (α : List (Fin 4))
    (a : ℕ → RationalSpaceTime) {y : SpaceTime} (ha : IsFastName a y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative c.val α y - rationalVector (c.evaluate α a ε hε)‖ ≤ (ε : ℝ) := by
  rw [← c.val_diffWord α]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr hε.le)).mpr
  intro j
  exact ((c j).diffWord α).evaluate_spec a ha ε hε

end NonperiodicVector
end ForcedComputation

end

end OAI
