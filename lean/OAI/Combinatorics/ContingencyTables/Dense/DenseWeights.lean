import OAI.Combinatorics.ContingencyTables.PublishedInputs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Continuous and dyadic bin weights

The actual floor-rounded weights used by the dense grid sampler. Convexity
of the penalty implies log-concavity of its density, and local changes of
the scaled penalty give explicit comparisons with the dyadic bin weights.
-/

namespace ContingencyTables.DenseWeights

noncomputable section

def density {X : Type*} (A : ℝ) (p : X → ℝ) (x : X) : ℝ :=
  (2 : ℝ) ^ (-(A * p x))

def binWeight {X : Type*} (A : ℝ) (p : X → ℝ) (v : X) : ℝ :=
  (2 : ℝ) ^ (-((⌊A * p v⌋ : ℤ) : ℝ))

theorem density_pos {X : Type*} (A : ℝ) (p : X → ℝ) (x : X) :
    0 < density A p x := Real.rpow_pos_of_pos (by norm_num) _

theorem binWeight_pos {X : Type*} (A : ℝ) (p : X → ℝ) (v : X) :
    0 < binWeight A p v := Real.rpow_pos_of_pos (by norm_num) _

/-- Rounding the exponent down changes a weight by at most a factor two. -/
theorem binWeight_comparison {X : Type*} (A : ℝ) (p : X → ℝ) (v : X) :
    density A p v ≤ binWeight A p v ∧ binWeight A p v ≤ 2 * density A p v := by
  have hlo := Int.floor_le (A * p v)
  have hhi := Int.lt_floor_add_one (A * p v)
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · calc
      binWeight A p v ≤ (2 : ℝ) ^ (-(A * p v) + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 * density A p v := by
        rw [Real.rpow_add (by norm_num)]
        simp [density, mul_comm]

/-- A scaled-penalty change at most `s` gives the tube density bound. -/
theorem density_le_binWeight {X : Type*} (A : ℝ) (p : X → ℝ)
    (x v : X) (s : ℝ) (hchange : |A * p x - A * p v| ≤ s) :
    density A p x ≤ (2 : ℝ) ^ s * binWeight A p v := by
  have hlo := Int.floor_le (A * p v)
  have h := (abs_le.mp hchange).1
  calc
    density A p x ≤ (2 : ℝ) ^ (s - (⌊A * p v⌋ : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 : ℝ) ^ s * binWeight A p v := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
      rfl

theorem binWeight_le_density {X : Type*} (A : ℝ) (p : X → ℝ)
    (x v : X) (s : ℝ) (hchange : |A * p x - A * p v| ≤ s) :
    binWeight A p v ≤ (2 : ℝ) ^ (s + 1) * density A p x := by
  have hhi := Int.lt_floor_add_one (A * p v)
  have h := (abs_le.mp hchange).2
  calc
    binWeight A p v ≤ (2 : ℝ) ^ ((s + 1) - A * p x) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = (2 : ℝ) ^ (s + 1) * density A p x := by
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
      rfl

theorem bin_density_comparison {X : Type*} (A : ℝ) (p : X → ℝ)
    (x v : X) (hchange : |A * p x - A * p v| ≤ 1) :
    binWeight A p v / 4 ≤ density A p x ∧ density A p x ≤ 2 * binWeight A p v := by
  have hl := binWeight_le_density A p x v 1 hchange
  have hu := density_le_binWeight A p x v 1 hchange
  norm_num at hl hu
  constructor <;> linarith

theorem tube_density_comparison {X : Type*} (A : ℝ) (p : X → ℝ)
    (x v : X) (hchange : |A * p x - A * p v| ≤ 2) :
    density A p x ≤ 4 * binWeight A p v := by
  have h := density_le_binWeight A p x v 2 hchange
  norm_num at h
  exact h

theorem density_continuous {X : Type*} [TopologicalSpace X]
    (A : ℝ) (p : X → ℝ) (hp : Continuous p) : Continuous (density A p) := by
  exact Real.continuous_const_rpow (by norm_num) |>.comp ((continuous_const.mul hp).neg)

/-- The continuous density used by the sampler is log-concave on every
convex domain on which its penalty is convex. -/
theorem density_logConcave {q : ℕ} (A : ℝ) (hA : 0 ≤ A)
    (p : PublishedInputs.Point q → ℝ) (K : Set (PublishedInputs.Point q))
    (hp : ConvexOn ℝ K p) : PublishedInputs.LogConcaveOn (density A p) K := by
  intro x hx y hy t ht ht₁
  have hc := hp.2 hx hy (sub_nonneg.mpr ht₁.le) ht.le (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul] at hc
  have he : (density A p x) ^ (1 - t) * (density A p y) ^ t =
      (2 : ℝ) ^ (-A * ((1 - t) * p x + t * p y)) := by
    simp only [density, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [he]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hc hA]

end

end ContingencyTables.DenseWeights

end OAI
