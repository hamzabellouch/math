import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Expanding
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CenterPaths

namespace OAI

noncomputable section
namespace VelocityDetection.Expanding
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem count_mono {K D : ℝ} (hK : 0 ≤ K) (hD : 1 ≤ D) : Monotone (count K D) := by
  intro n m hnm
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hnm) hK

theorem spacing_pos {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) (n : ℕ) :
    0 < spacing ν K D n := by
  have := radius_ge_one hν hK hD n
  dsimp [spacing]
  linarith

theorem spacing_next_ge {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) (n : ℕ) :
    spacing ν K D n ≤ spacing ν K D (n + 1) := by
  have := radius_next_ge hν hK hD n
  have := radius_ge_one hν hK hD n
  dsimp [spacing]
  linarith

theorem path_coordinate_bounds {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D)
    (n : ℕ) {k l : ℕ} (hk : (k : ℝ) ≤ count K D n)
    (hl : (l : ℝ) ≤ count K D (n + 1)) {σ : ℝ} (hσ : |σ| ≤ 1) :
    |spacing ν K D n| ≤ duration ν K D n ∧
    |spacing ν K D n * k| ≤ duration ν K D n ∧
    |spacing ν K D (n + 1) * l| ≤ duration ν K D n ∧
    |CenterPaths.privateRow (spacing ν K D n) k| ≤ duration ν K D n ∧
    |σ * spacing ν K D (n + 1)| ≤ duration ν K D n := by
  have hS := (spacing_pos hν hK hD n).le
  have hS' := (spacing_pos hν hK hD (n + 1)).le
  have hSS := spacing_next_ge hν hK hD n
  have hc := count_mono hK hD (Nat.le_succ n)
  have hC : 0 ≤ count K D (n + 1) := by dsimp [count]; positivity
  have hond : spacing ν K D (n + 1) ≤ duration ν K D n := by
    dsimp [duration]
    nlinarith
  have hy : |CenterPaths.privateRow (spacing ν K D n) k| ≤ duration ν K D n := by
    rw [CenterPaths.privateRow, abs_mul, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg hS]
    calc
      _ ≤ (count K D (n + 1) + 2) * spacing ν K D n :=
        mul_le_mul_of_nonneg_right (by linarith) hS
      _ ≤ (count K D (n + 1) + 2) * spacing ν K D (n + 1) :=
        mul_le_mul_of_nonneg_left hSS (by positivity)
      _ = _ := by dsimp [duration]; ring
  refine ⟨?_, ?_, ?_, hy, ?_⟩
  · rw [abs_of_nonneg hS]; exact hSS.trans hond
  · rw [abs_of_nonneg (mul_nonneg hS (Nat.cast_nonneg k))]
    have := mul_le_mul_of_nonneg_left (show (k : ℝ) ≤ count K D (n + 1) + 2 by linarith) hS'
    have := mul_le_mul_of_nonneg_right hSS (Nat.cast_nonneg k)
    dsimp [duration]
    linarith
  · rw [abs_of_nonneg (mul_nonneg hS' (Nat.cast_nonneg l))]
    have := mul_le_mul_of_nonneg_left hl hS'
    dsimp [duration]
    linarith
  · rw [abs_mul, abs_of_nonneg hS']
    exact (mul_le_mul_of_nonneg_right hσ hS').trans (by simpa using hond)

theorem startTime_strictMono {ν K D : ℝ} (hν : 0 < ν) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    StrictMono (startTime ν K D) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [startTime]
  linarith [duration_ge_one hν hK hD n]

end VelocityDetection.Expanding
end

end OAI
