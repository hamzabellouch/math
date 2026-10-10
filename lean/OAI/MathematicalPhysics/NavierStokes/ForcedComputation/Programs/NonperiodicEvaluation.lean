import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicRationalEvaluation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedEvaluation

namespace OAI

/-! Evaluation of a finite moving-gate expression at a fast Cauchy name.
A coordinate box read from its zeroth approximation supplies a rational
Lipschitz bound and hence an explicit finite input precision. -/

noncomputable section
namespace ForcedComputation.NonperiodicExpr
open ShearFlows
open scoped BigOperators

def nameRadius (a : ℕ → RationalSpaceTime) : ℚ :=
  (∑ j : Fin 4, |rationalCoord j (a 0)|) + 2

theorem nameRadius_bounds {a : ℕ → RationalSpaceTime} {y : SpaceTime}
    (ha : IsFastName a y) (n : ℕ) :
    (∀ j, |timeSpaceCoord j y| ≤ |(nameRadius a : ℝ)|) ∧
    (∀ j, |timeSpaceCoord j (rationalPoint (a n))| ≤ |(nameRadius a : ℝ)|) := by
  have hr : (0 : ℝ) ≤ nameRadius a := by
    exact_mod_cast (show (0 : ℚ) ≤ nameRadius a by unfold nameRadius; positivity)
  have hq (j : Fin 4) : |(rationalCoord j (a 0) : ℝ)| + 2 ≤ (nameRadius a : ℝ) := by
    have hq : |rationalCoord j (a 0)| + 2 ≤ nameRadius a := by
      unfold nameRadius
      have hs := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
        abs_nonneg (rationalCoord i (a 0))) (Finset.mem_univ j)
      linarith
    exact_mod_cast hq
  have hd (j : Fin 4) (k : ℕ) :
      |timeSpaceCoord j y - (rationalCoord j (a k) : ℝ)| ≤ 1 := by
    have h := (timeSpaceCoord_norm j (y - rationalPoint (a k))).trans
      ((ha k).trans (ClockedExpr.errorTolerance_le_one k))
    simpa only [map_sub, timeSpaceCoord_rational, Real.norm_eq_abs] using h
  have hy (j : Fin 4) : |timeSpaceCoord j y| ≤ |(rationalCoord j (a 0) : ℝ)| + 1 := by
    have h := abs_add_le (timeSpaceCoord j y - (rationalCoord j (a 0) : ℝ))
      (rationalCoord j (a 0) : ℝ)
    rw [sub_add_cancel] at h
    linarith [hd j 0]
  constructor
  · intro j
    rw [abs_of_nonneg hr]
    linarith [hy j, hq j]
  · intro j
    rw [timeSpaceCoord_rational, abs_of_nonneg hr]
    have h := abs_add_le ((rationalCoord j (a n) : ℝ) - timeSpaceCoord j y) (timeSpaceCoord j y)
    rw [sub_add_cancel, abs_sub_comm] at h
    linarith [hd j n, hy j, hq j]

def inputPrecision (e : NonperiodicExpr) (M ε : ℚ) : ℕ :=
  ⌈2 * e.derivativeBound M / ε⌉₊ + 1

theorem inputPrecision_spec (e : NonperiodicExpr) (M : ℚ) {ε : ℚ} (hε : 0 < ε) :
    (e.derivativeBound M : ℝ) * errorTolerance (e.inputPrecision M ε) ≤ (ε : ℝ) / 2 := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  have hn : 2 * (e.derivativeBound M : ℝ) / ε ≤ (e.inputPrecision M ε : ℝ) := by
    have h : 2 * e.derivativeBound M / ε ≤ (e.inputPrecision M ε : ℚ) :=
      (Nat.le_ceil _).trans (by simp [inputPrecision])
    exact_mod_cast h
  have hp : (e.inputPrecision M ε : ℝ) ≤ (2 : ℝ) ^ (e.inputPrecision M ε) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := e.inputPrecision M ε)).le
  have hpow : (0 : ℝ) < 2 ^ (e.inputPrecision M ε) := by positivity
  rw [errorTolerance, ← div_eq_mul_inv]
  apply (div_le_iff₀ hpow).mpr
  have h := (div_le_iff₀ he).mp (hn.trans hp)
  linarith

def evaluate (e : NonperiodicExpr) (a : ℕ → RationalSpaceTime) (ε : ℚ) (hε : 0 < ε) : ℚ :=
  e.evaluateRational (a (e.inputPrecision (nameRadius a) ε)) (ε / 2) (by positivity)

theorem evaluate_spec (e : NonperiodicExpr) (a : ℕ → RationalSpaceTime)
    {y : SpaceTime} (ha : IsFastName a y) (ε : ℚ) (hε : 0 < ε) :
    |e.val y - (e.evaluate a ε hε : ℝ)| ≤ (ε : ℝ) := by
  let n := e.inputPrecision (nameRadius a) ε
  let q := a n
  obtain ⟨hy, hq⟩ := nameRadius_bounds ha n
  calc
    _ ≤ |e.val y - e.val (rationalPoint q)| +
        |e.val (rationalPoint q) - (e.evaluate a ε hε : ℝ)| := abs_sub_le _ _ _
    _ ≤ (ε : ℝ) / 2 + (ε : ℝ) / 2 := by
      apply add_le_add
      · exact (e.lipschitz_bound (nameRadius a) y (rationalPoint q) hy hq).trans
          ((mul_le_mul_of_nonneg_left (ha n)
            (Rat.cast_nonneg.mpr (e.derivativeBound_nonneg _))).trans
            (e.inputPrecision_spec (nameRadius a) hε))
      · simpa only [evaluate, Rat.cast_div, Rat.cast_ofNat] using
          e.evaluateRational_spec q (ε / 2) (by positivity)
    _ = _ := by ring

theorem evaluate_mixed_spec (e : NonperiodicExpr) (α : List (Fin 4))
    (a : ℕ → RationalSpaceTime) {y : SpaceTime} (ha : IsFastName a y)
    (ε : ℚ) (hε : 0 < ε) :
    |ClockedExpr.scalarMixed e.val α y - ((e.diffWord α).evaluate a ε hε : ℝ)| ≤ (ε : ℝ) := by
  rw [← e.val_diffWord α]
  exact (e.diffWord α).evaluate_spec a ha ε hε

end ForcedComputation.NonperiodicExpr

end

end OAI
