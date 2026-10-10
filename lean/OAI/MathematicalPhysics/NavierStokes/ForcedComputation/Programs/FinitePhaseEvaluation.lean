import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedVelocityEvaluation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmicBounds

namespace OAI

/-! Finite recursive evaluation of the Euler derivative polynomials that
occur in the logarithmic slowdown. -/

namespace ForcedComputation
open ShearFlows
open scoped ContDiff

def IsFastVectorName (a : ℕ → RationalVector) (v : Space) : Prop :=
  ∀ n, ‖v - rationalVector (a n)‖ ≤ errorTolerance n

theorem initializedVelocityTolerance_pos (n : ℕ) :
    0 < (2 : ℚ) ^ (-(n : ℤ)) := by positivity

def initializedVelocityName (loader body : Input)
    (hl : ValidInput loader) (hb : ValidInput body) (α : List (Fin 4))
    (b : ℕ → RationalSpaceTime) : ℕ → RationalVector := fun n =>
  evaluateInitializedVelocity loader body hl hb α b ((2 : ℚ) ^ (-(n : ℤ))) (initializedVelocityTolerance_pos n)

theorem initializedVelocityName_spec {loader body : Input}
    (hl : ValidInput loader) (hb : ValidInput body) (α : List (Fin 4))
    {b : ℕ → RationalSpaceTime} {y : SpaceTime} (hy : IsFastName b y) :
    IsFastVectorName (initializedVelocityName loader body hl hb α b)
      (mixedDerivative (initializedProgram loader body) α y) := by
  intro n
  have h := evaluateInitializedVelocity_spec hl hb α hy
    ((2 : ℚ) ^ (-(n : ℤ))) (by positivity)
  simpa [initializedVelocityName, errorTolerance] using h

def subtractNatName (c : ℕ) (a b : ℕ → RationalVector) : ℕ → RationalVector :=
  fun n => a (n + c + 1) - (c : ℚ) • b (n + c + 1)

theorem subtractNatName_spec {a b : ℕ → RationalVector} {x y : Space}
    (ha : IsFastVectorName a x) (hb : IsFastVectorName b y) (c : ℕ) :
    IsFastVectorName (subtractNatName c a b) (x - (c : ℝ) • y) := by
  intro n
  have hcast (m : ℕ) : rationalVector (a m - (c : ℚ) • b m) =
      rationalVector (a m) - (c : ℝ) • rationalVector (b m) := by
    ext j
    simp only [rationalVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast]
  have hsize : (1 + (c : ℝ)) ≤ (2 : ℝ) ^ (c + 1) := by
    have h := Nat.lt_two_pow_self (n := c + 1)
    rw [add_comm 1]
    exact_mod_cast h.le
  have ht : (1 + (c : ℝ)) * errorTolerance (n + c + 1) ≤ errorTolerance n := by
    calc
      _ ≤ (2 : ℝ) ^ (c + 1) * errorTolerance (n + c + 1) :=
        mul_le_mul_of_nonneg_right hsize (by dsimp [errorTolerance]; positivity)
      _ = errorTolerance n := by
        simp only [errorTolerance, show n + c + 1 = n + (c + 1) by omega,
          pow_add, mul_inv_rev]
        field_simp
  rw [subtractNatName, hcast]
  have he : x - (c : ℝ) • y - (rationalVector (a (n + c + 1)) -
      (c : ℝ) • rationalVector (b (n + c + 1))) =
      (x - rationalVector (a (n + c + 1))) -
        (c : ℝ) • (y - rationalVector (b (n + c + 1))) := by module
  rw [he]
  calc
    _ ≤ ‖x - rationalVector (a (n + c + 1))‖ +
        ‖(c : ℝ) • (y - rationalVector (b (n + c + 1)))‖ := norm_sub_le _ _
    _ ≤ errorTolerance (n + c + 1) + (c : ℝ) * errorTolerance (n + c + 1) := by
      rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg c)]
      exact add_le_add (ha _) (mul_le_mul_of_nonneg_left (hb _) (Nat.cast_nonneg c))
    _ = (1 + (c : ℝ)) * errorTolerance (n + c + 1) := by ring
    _ ≤ _ := ht

def phaseName (r : ℕ) (a : ℕ → ℕ → RationalVector) : ℕ → ℕ → ℕ → RationalVector
  | 0, k => a k
  | n + 1, k => subtractNatName (r + n) (phaseName r a n (k + 1)) (phaseName r a n k)

theorem phaseName_spec (r : ℕ) {A : ℝ → Space} (hA : ContDiff ℝ ∞ A) (s : ℝ)
    {a : ℕ → ℕ → RationalVector}
    (ha : ∀ k, IsFastVectorName (a k) (iteratedDeriv k A s)) (n k : ℕ) :
    IsFastVectorName (phaseName r a n k) (iteratedDeriv k (phaseIter r A n) s) := by
  induction n generalizing k with
  | zero => exact ha k
  | succ n ih =>
    rw [show phaseIter r A (n + 1) =
      phaseDerivative (r + n) (phaseIter r A n) from rfl,
      iteratedDeriv_phaseDerivative (r + n) k (phaseIter_smooth r hA n)]
    exact subtractNatName_spec (ih (k + 1)) (ih k) (r + n)

end ForcedComputation

end OAI
