import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedEvaluation

namespace OAI

/-! Vector-valued finite clocked programs, with certified evaluation and
bounds for every ordered mixed derivative on finite time slabs. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped ContDiff BigOperators

abbrev ClockedVector := Fin 3 → ClockedExpr

namespace ClockedVector

def Valid (c : ClockedVector) : Prop := ∀ j, (c j).Valid

def val (c : ClockedVector) : Velocity := fun y j => (c j).val y

def diffWord (c : ClockedVector) (α : List (Fin 4)) : ClockedVector :=
  fun j => (c j).diffWord α

theorem valid_diffWord {c : ClockedVector} (hc : c.Valid) (α : List (Fin 4)) :
    (c.diffWord α).Valid := fun j => (c j).valid_diffWord (hc j) α

theorem smooth {c : ClockedVector} (hc : c.Valid) : ContDiff ℝ ∞ c.val :=
  contDiff_pi.mpr (fun j => (c j).smooth (hc j))

theorem val_diffWord {c : ClockedVector} (hc : c.Valid) (α : List (Fin 4)) :
    (c.diffWord α).val = mixedDerivative c.val α := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext y j
    rw [mixedDerivative, ← ih]
    have h := fderiv_pi (fun k =>
      (((c k).diffWord α).smooth ((c k).valid_diffWord (hc k) α)).differentiable (by simp) y)
    change ((c j).diffWord (i :: α)).val y =
      (fderiv ℝ (c.diffWord α).val y (spaceTimeDirection i)) j
    change fderiv ℝ (c.diffWord α).val y = _ at h
    rw [h]
    exact ((c j).diffWord α).val_diff ((c j).valid_diffWord (hc j) α) i y

def bound (c : ClockedVector) (α : List (Fin 4)) (M : ℚ) : ℚ :=
  ∑ j, ((c j).diffWord α).bound M

theorem bound_nonneg (c : ClockedVector) (α : List (Fin 4)) (M : ℚ) :
    0 ≤ c.bound α M :=
  Finset.sum_nonneg (fun j _ => ((c j).diffWord α).bound_nonneg M)

theorem val_bound {c : ClockedVector} (hc : c.Valid) (α : List (Fin 4))
    (M : ℚ) (y : SpaceTime) (hy : |y.1| ≤ |(M : ℝ)|) :
    ‖mixedDerivative c.val α y‖ ≤ (c.bound α M : ℝ) := by
  rw [← val_diffWord hc]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr (c.bound_nonneg α M))).mpr
  intro j
  have hj := ((c j).diffWord α).val_bound ((c j).valid_diffWord (hc j) α) M y hy
  apply hj.trans
  exact_mod_cast Finset.single_le_sum
    (fun k _ => ((c k).diffWord α).bound_nonneg M) (Finset.mem_univ j)

def evaluate (c : ClockedVector) (hc : c.Valid) (α : List (Fin 4))
    (a : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  fun j => ((c j).diffWord α).evaluate ((c j).valid_diffWord (hc j) α) a ε hε

theorem evaluate_spec {c : ClockedVector} (hc : c.Valid) (α : List (Fin 4))
    (a : ℕ → RationalSpaceTime) {y : SpaceTime} (ha : IsFastName a y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative c.val α y - rationalVector (c.evaluate hc α a ε hε)‖ ≤ (ε : ℝ) := by
  rw [← val_diffWord hc]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr hε.le)).mpr
  intro j
  exact ((c j).diffWord α).evaluate_spec ((c j).valid_diffWord (hc j) α) a ha ε hε

end ClockedVector
end ForcedComputation

end

end OAI
