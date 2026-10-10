import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedLipschitz
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedRationalEvaluation

namespace OAI

/-! Evaluation at a named real point uses a time slab obtained from the
zeroth approximation. The derivative bound on this slab gives a finite
input precision for every mixed derivative. -/

noncomputable section
namespace ForcedComputation.ClockedExpr
open ShearFlows

def nameRadius (a : ℕ → RationalSpaceTime) : ℚ := |(a 0).1| + 2

theorem errorTolerance_le_one (n : ℕ) : errorTolerance n ≤ 1 := by
  unfold errorTolerance
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem nameRadius_bounds {a : ℕ → RationalSpaceTime} {y : SpaceTime}
    (ha : IsFastName a y) (n : ℕ) :
    |y.1| ≤ |(nameRadius a : ℝ)| ∧
      |(rationalPoint (a n)).1| ≤ |(nameRadius a : ℝ)| := by
  have hzero : |y.1 - ((a 0).1 : ℝ)| ≤ 1 :=
    (norm_fst_le (y - rationalPoint (a 0))).trans
      ((ha 0).trans (errorTolerance_le_one 0))
  have hn : |y.1 - ((a n).1 : ℝ)| ≤ 1 :=
    (norm_fst_le (y - rationalPoint (a n))).trans
      ((ha n).trans (errorTolerance_le_one n))
  have hy : |y.1| ≤ |((a 0).1 : ℝ)| + 1 := by
    have h := abs_add_le (y.1 - ((a 0).1 : ℝ)) ((a 0).1 : ℝ)
    rw [sub_add_cancel] at h
    linarith
  have hq : |((a n).1 : ℝ)| ≤ |((a 0).1 : ℝ)| + 2 := by
    have h := abs_add_le (((a n).1 : ℝ) - y.1) y.1
    rw [sub_add_cancel, abs_sub_comm ((a n).1 : ℝ) y.1] at h
    linarith
  have hr : (nameRadius a : ℝ) = |((a 0).1 : ℝ)| + 2 := by
    simp only [nameRadius, Rat.cast_add, Rat.cast_abs, Rat.cast_ofNat]
  rw [hr, abs_of_nonneg (show 0 ≤ |((a 0).1 : ℝ)| + 2 by positivity)]
  exact ⟨by linarith, hq⟩

def inputPrecision (e : ClockedExpr) (M ε : ℚ) : ℕ :=
  ⌈2 * e.derivativeBound M / ε⌉₊ + 1

theorem inputPrecision_spec (e : ClockedExpr) (M : ℚ) {ε : ℚ} (hε : 0 < ε) :
    (e.derivativeBound M : ℝ) * errorTolerance (e.inputPrecision M ε) ≤ (ε : ℝ) / 2 := by
  have he : (0 : ℝ) < ε := by exact_mod_cast hε
  have hn : 2 * (e.derivativeBound M : ℝ) / ε ≤ (e.inputPrecision M ε : ℝ) := by
    have h : 2 * e.derivativeBound M / ε ≤ (e.inputPrecision M ε : ℚ) :=
      (Nat.le_ceil _).trans (by simp [inputPrecision])
    exact_mod_cast h
  have hp : (e.inputPrecision M ε : ℝ) ≤ (2 : ℝ) ^ (e.inputPrecision M ε) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := e.inputPrecision M ε)).le
  have hle := hn.trans hp
  have hpow : (0 : ℝ) < 2 ^ (e.inputPrecision M ε) := by positivity
  rw [errorTolerance, ← div_eq_mul_inv]
  apply (div_le_iff₀ hpow).mpr
  have h := (div_le_iff₀ he).mp hle
  linarith

def evaluate (e : ClockedExpr) (he : e.Valid) (a : ℕ → RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : ℚ :=
  e.evaluateRational he (a (e.inputPrecision (nameRadius a) ε)) (ε / 2) (by positivity)

theorem evaluate_spec {e : ClockedExpr} (he : e.Valid)
    (a : ℕ → RationalSpaceTime) {y : SpaceTime} (ha : IsFastName a y)
    (ε : ℚ) (hε : 0 < ε) :
    |e.val y - (e.evaluate he a ε hε : ℝ)| ≤ (ε : ℝ) := by
  let n := e.inputPrecision (nameRadius a) ε
  let q := a n
  obtain ⟨hy, hq⟩ := nameRadius_bounds ha n
  calc
    _ ≤ |e.val y - e.val (rationalPoint q)| +
        |e.val (rationalPoint q) - (e.evaluate he a ε hε : ℝ)| := abs_sub_le _ _ _
    _ ≤ (ε : ℝ) / 2 + (ε : ℝ) / 2 := by
      apply add_le_add
      · exact (lipschitz_bound he (nameRadius a) y (rationalPoint q) hy hq).trans
          ((mul_le_mul_of_nonneg_left (ha n)
            (Rat.cast_nonneg.mpr (e.derivativeBound_nonneg _))).trans
            (inputPrecision_spec e (nameRadius a) hε))
      · simpa only [evaluate, Rat.cast_div, Rat.cast_ofNat] using
          e.evaluateRational_spec he q (ε / 2) (by positivity)
    _ = _ := by ring

theorem evaluate_mixed_spec {e : ClockedExpr} (he : e.Valid) (α : List (Fin 4))
    (a : ℕ → RationalSpaceTime) {y : SpaceTime} (ha : IsFastName a y)
    (ε : ℚ) (hε : 0 < ε) :
    |scalarMixed e.val α y -
      ((e.diffWord α).evaluate (e.valid_diffWord he α) a ε hε : ℝ)| ≤ (ε : ℝ) := by
  rw [← e.val_diffWord he α]
  exact evaluate_spec (e.valid_diffWord he α) a ha ε hε

end ForcedComputation.ClockedExpr

end

end OAI
