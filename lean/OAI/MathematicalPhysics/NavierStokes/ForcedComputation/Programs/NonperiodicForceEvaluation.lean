import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicResidual

namespace OAI

/-! The viscosity enters the residual linearly. A finite box bound supplies
an explicit precision for its real name, so evaluation remains terminating. -/

noncomputable section
namespace ForcedComputation.NonperiodicResidual
open ShearFlows
open scoped ContDiff BigOperators

def laplaceBound (c : NonperiodicVector) (α : List (Fin 4)) (M : ℚ) : ℚ :=
  ∑ j : Fin 3, c.bound (α ++ [j.succ,j.succ]) M

theorem laplaceBound_nonneg (c : NonperiodicVector) (α : List (Fin 4)) (M : ℚ) :
    0 ≤ laplaceBound c α M := Finset.sum_nonneg (fun _ _ => c.bound_nonneg _ _)

theorem laplaceBound_spec (c : NonperiodicVector) (α : List (Fin 4)) (M : ℚ)
    (y : SpaceTime) (hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) :
    ‖∑ j : Fin 3, mixedDerivative c.val (α ++ [j.succ,j.succ]) y‖ ≤
      (laplaceBound c α M : ℝ) := by
  apply (norm_sum_le _ _).trans
  simpa only [laplaceBound, Rat.cast_sum] using
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => c.val_bound _ M y hy)

theorem coefficient_error (c : NonperiodicVector) (α : List (Fin 4)) (M : ℚ)
    (y : SpaceTime) (hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)|) (ν r : ℝ) :
    ‖mixedDerivative (residual ν c.val) α y -
      mixedDerivative (residual r c.val) α y‖ ≤
      |ν-r| * (laplaceBound c α M : ℝ) := by
  rw [residual_eq_force_add, residual_eq_force_add,
    mixedDerivative_add (force_smooth c.smooth ν) (convectiveField_smooth c.smooth),
    mixedDerivative_add (force_smooth c.smooth r) (convectiveField_smooth c.smooth)]
  simp only [Pi.add_apply, add_sub_add_right_eq_sub]
  rw [mixedDerivative_force c.smooth, mixedDerivative_force c.smooth]
  have he {v w : Space} : (v - ν • w) - (v - r • w) = (r-ν) • w := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_mul_of_nonneg_left (laplaceBound_spec c α M y hy) (abs_nonneg _)

def coefficientPrecision (c : NonperiodicVector) (α : List (Fin 4)) (M ε : ℚ) : ℕ :=
  ⌈2 * laplaceBound c α M / ε⌉₊ + 1

theorem coefficientPrecision_spec (c : NonperiodicVector) (α : List (Fin 4))
    (M : ℚ) {ε : ℚ} (hε : 0 < ε) :
    errorTolerance (coefficientPrecision c α M ε) * (laplaceBound c α M : ℝ) ≤
      (ε : ℝ) / 2 := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  have hn : 2 * (laplaceBound c α M : ℝ) / ε ≤
      (coefficientPrecision c α M ε : ℝ) := by
    have hh : 2 * laplaceBound c α M / ε ≤ (coefficientPrecision c α M ε : ℚ) :=
      (Nat.le_ceil _).trans (by simp [coefficientPrecision])
    exact_mod_cast hh
  have hp : (coefficientPrecision c α M ε : ℝ) ≤
      (2 : ℝ) ^ (coefficientPrecision c α M ε) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := coefficientPrecision c α M ε)).le
  have hle := hn.trans hp
  have h2 : (0 : ℝ) < 2 ^ (coefficientPrecision c α M ε) := by positivity
  rw [errorTolerance, mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ h2).mpr
  have hh := (div_le_iff₀ he).mp hle
  linarith

def evaluate (c : NonperiodicVector) (α : List (Fin 4))
    (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  let M := NonperiodicExpr.nameRadius b
  let r := a (coefficientPrecision c α M ε)
  (code c r).evaluate α b (ε/2) (by positivity)

theorem evaluate_spec (c : NonperiodicVector) (α : List (Fin 4))
    {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    {y : SpaceTime} {b : ℕ → RationalSpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (residual ν c.val) α y -
      rationalVector (evaluate c α a b ε hε)‖ ≤ (ε : ℝ) := by
  let M := NonperiodicExpr.nameRadius b
  let r := a (coefficientPrecision c α M ε)
  have hy : ∀ j, |timeSpaceCoord j y| ≤ |(M : ℝ)| :=
    fun j => (NonperiodicExpr.nameRadius_bounds hb 0).1 j
  calc
    _ ≤ ‖mixedDerivative (residual ν c.val) α y - mixedDerivative (residual r c.val) α y‖ +
        ‖mixedDerivative (residual r c.val) α y -
          rationalVector (evaluate c α a b ε hε)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (ε : ℝ)/2 + (ε : ℝ)/2 := by
      apply add_le_add
      · exact (coefficient_error c α M y hy ν r).trans
          ((mul_le_mul_of_nonneg_right (ha _)
            (Rat.cast_nonneg.mpr (laplaceBound_nonneg c α M))).trans
              (coefficientPrecision_spec c α M hε))
      · simpa only [evaluate, val, Rat.cast_div, Rat.cast_ofNat] using
          (code c r).evaluate_spec α b hb (ε/2) (by positivity)
    _ = _ := by ring

end ForcedComputation.NonperiodicResidual

end

end OAI
