import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model

namespace OAI

/-!
# Explicit rational rounding and distinctness

Rounding on a common rational grid controls the approximation error and
preserves pairwise distinctness of separated nuclear positions.
-/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators

def roundCoordinate (denominator : ℕ) (x : ℝ) : ℚ :=
  (Int.floor ((denominator : ℝ) * x) : ℚ) / (denominator : ℚ)

def roundPosition (denominator : ℕ) (x : Position) : Fin 3 → ℚ :=
  fun a => roundCoordinate denominator (x a)

/-- A common denominator bounds each coordinate error, also for negative data. -/
theorem roundCoordinate_error {denominator : ℕ} (hdenom : 0 < denominator) (x : ℝ) :
    |(roundCoordinate denominator x : ℝ) - x| ≤ 1 / (denominator : ℝ) := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast hdenom
  have hl := Int.floor_le ((denominator : ℝ) * x)
  have hu := Int.lt_floor_add_one ((denominator : ℝ) * x)
  have heq : (roundCoordinate denominator x : ℝ) - x =
      ((Int.floor ((denominator : ℝ) * x) : ℝ) - (denominator : ℝ) * x) /
        (denominator : ℝ) := by
    simp only [roundCoordinate, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    field_simp
  rw [heq, abs_div, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  apply abs_le.mpr
  constructor <;> linarith

/-- A deliberately coarse Euclidean bound suffices for the rounding budget. -/
theorem roundPosition_error {denominator : ℕ} (hdenom : 0 < denominator) (x : Position) :
    ‖realPosition (roundPosition denominator x) - x‖ ≤ 3 / (denominator : ℝ) := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast hdenom
  have hcoord (a : Fin 3) :
      ((realPosition (roundPosition denominator x) - x) a) ^ 2 ≤
        (1 / (denominator : ℝ)) ^ 2 := by
    have h := roundCoordinate_error hdenom (x a)
    change |((realPosition (roundPosition denominator x) - x) a)| ≤
      1 / (denominator : ℝ) at h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h
  have hsq : ‖realPosition (roundPosition denominator x) - x‖ ^ 2 ≤
      3 * (1 / (denominator : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => hcoord a
    simpa using h
  have hc : (3 / (denominator : ℝ)) ^ 2 = 9 * (1 / (denominator : ℝ)) ^ 2 := by ring
  have hn := norm_nonneg (realPosition (roundPosition denominator x) - x)
  have hpos : 0 ≤ 3 / (denominator : ℝ) := by positivity
  nlinarith [sq_nonneg (1 / (denominator : ℝ))]

/-- Rounding preserves distinct nuclei when the common grid is finer than
one sixth of every original pair separation. -/
theorem roundPosition_injective {m denominator : ℕ} (hdenom : 0 < denominator)
    (position : Fin m → Position)
    (hsep : ∀ i j, i ≠ j → 6 / (denominator : ℝ) < ‖position i - position j‖) :
    Function.Injective (fun i => roundPosition denominator (position i)) := by
  intro i j hij
  by_contra hne
  have hi := roundPosition_error hdenom (position i)
  have hj := roundPosition_error hdenom (position j)
  have hr : realPosition (roundPosition denominator (position i)) =
      realPosition (roundPosition denominator (position j)) := congrArg realPosition hij
  have htriangle : ‖position i - position j‖ ≤
      ‖realPosition (roundPosition denominator (position i)) - position i‖ +
      ‖realPosition (roundPosition denominator (position j)) - position j‖ := by
    calc
      ‖position i - position j‖ ≤
          ‖position i - realPosition (roundPosition denominator (position i))‖ +
          ‖realPosition (roundPosition denominator (position i)) - position j‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = _ := by rw [norm_sub_rev (position i) (realPosition (roundPosition denominator (position i))), hr]
  have h := hsep i j hne
  have hbudget : 3 / (denominator : ℝ) + 3 / (denominator : ℝ) =
      6 / (denominator : ℝ) := by ring
  linarith

end ContinuumCoulomb

end

end OAI
