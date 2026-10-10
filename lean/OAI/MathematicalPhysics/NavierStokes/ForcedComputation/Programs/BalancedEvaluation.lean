import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.BalancedFiniteCode

namespace OAI

/-! The zeroth time approximation selects a finite translate window with
one unit of spare width. Evaluation of every residual jet is then the
existing terminating finite-expression evaluator, including a viscosity
name when viscosity is not rational. -/

noncomputable section
namespace ForcedComputation.BalancedExpressions
open ShearFlows Set Filter
open scoped Topology

def windowLower (b : ℕ → RationalSpaceTime) : ℚ := (b 0).1 - 2
def windowUpper (b : ℕ → RationalSpaceTime) : ℚ := (b 0).1 + 2

theorem named_window {b : ℕ → RationalSpaceTime} {y : SpaceTime}
    (hb : IsFastName b y) : y.1 ∈ Ioo (windowLower b : ℝ) (windowUpper b) := by
  have h := (norm_fst_le (y-rationalPoint (b 0))).trans (hb 0)
  change |y.1 - ((b 0).1 : ℝ)| ≤ errorTolerance 0 at h
  norm_num [errorTolerance] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  simp only [windowLower, windowUpper, Rat.cast_sub, Rat.cast_add, Rat.cast_ofNat]
  constructor <;> linarith

def evaluate (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  NonperiodicResidual.evaluate (code I hI (windowLower b) (windowUpper b)) α a b ε hε

theorem evaluate_spec (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (α : List (Fin 4)) {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    {y : SpaceTime} {b : ℕ → RationalSpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (residual ν (BalancedVelocity.velocity I hI)) α y -
      rationalVector (evaluate I hI α a b ε hε)‖ ≤ (ε : ℝ) := by
  have hg := code_germ I hI (windowLower b) (windowUpper b) (named_window hb)
  have hj := (mixedDerivative_eventuallyEq (residual_eventuallyEq hg ν) α).self_of_nhds
  rw [← hj]
  exact NonperiodicResidual.evaluate_spec _ α ha hb ε hε

def boxForceBound (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (α : List (Fin 4)) (u v M : ℚ) (a : ℕ → ℚ) : ℕ :=
  let c := code I hI u v
  ⌈(NonperiodicResidual.code c 0).bound α M +
    (|a 0|+1) * NonperiodicResidual.laplaceBound c α M⌉₊

theorem boxForceBound_spec (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (α : List (Fin 4)) (u v M : ℚ) {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    (y : SpaceTime) (ht : y.1 ∈ Ioo (u : ℝ) v)
    (hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) :
    ‖mixedDerivative (residual ν (BalancedVelocity.velocity I hI)) α y‖ ≤
      (boxForceBound I hI α u v M a : ℝ) := by
  let c := code I hI u v
  have hg := code_germ I hI u v ht
  have hj := (mixedDerivative_eventuallyEq (residual_eventuallyEq hg ν) α).self_of_nhds
  have hν : |ν| ≤ |((a 0) : ℝ)|+1 := by
    have ha0 := ha 0
    norm_num [errorTolerance] at ha0
    linarith [abs_sub_abs_le_abs_sub ν (a 0)]
  rw [← hj]
  calc
    _ ≤ ‖mixedDerivative (residual 0 c.val) α y‖ +
        ‖mixedDerivative (residual ν c.val) α y - mixedDerivative (residual 0 c.val) α y‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub
        (mixedDerivative (residual 0 c.val) α y) (mixedDerivative (residual ν c.val) α y)
    _ ≤ ((NonperiodicResidual.code c 0).bound α M : ℝ) +
        (|((a 0) : ℝ)|+1) * (NonperiodicResidual.laplaceBound c α M : ℝ) := by
      apply add_le_add
      · simpa only [NonperiodicResidual.val, Rat.cast_zero] using
          (NonperiodicResidual.code c 0).val_bound α M y hy
      · exact (NonperiodicResidual.coefficient_error c α M y hy ν 0).trans
          (by simpa only [sub_zero] using (mul_le_mul_of_nonneg_right hν
            (Rat.cast_nonneg.mpr (NonperiodicResidual.laplaceBound_nonneg c α M))))
    _ ≤ _ := by
      exact_mod_cast Nat.le_ceil ((NonperiodicResidual.code c 0).bound α M +
        (|a 0|+1) * NonperiodicResidual.laplaceBound c α M)

end ForcedComputation.BalancedExpressions

end

end OAI
