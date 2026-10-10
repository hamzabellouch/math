import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace OAI

/-! The rational widths and burst durations in the compact velocity
detector. Index `n` below denotes manuscript block `n + 1`. -/

namespace ForcedComputation.VelocityDetector
open scoped BigOperators

def expansion (L : ℕ) : ℕ := 4 ^ L

def geometricRatio (L : ℕ) : ℚ := 1 / (2 * (expansion L : ℚ))

def width (L n : ℕ) : ℚ := (1 / 1000000) * geometricRatio L ^ (n + 1)

def laplacianBound (C L n : ℕ) : ℚ :=
  2 * C * (width L n)⁻¹ ^ 2 * (1 + (n + 1) * L) * (expansion L : ℚ) ^ (3 * (n + 1))

def duration (C L n : ℕ) : ℚ := 1 / (100 * (1 + laplacianBound C L n))

def massBound (L : ℕ) : ℚ :=
  4 * (1 / 1000000) ^ 2 * geometricRatio L ^ 2 / (1 - geometricRatio L ^ 2)

theorem expansion_pos (L : ℕ) : 0 < expansion L := pow_pos (by norm_num) L

theorem expansion_one_le (L : ℕ) : 1 ≤ expansion L := expansion_pos L

theorem geometricRatio_pos (L : ℕ) : 0 < geometricRatio L := by
  unfold geometricRatio
  have h : (0 : ℚ) < expansion L := by exact_mod_cast expansion_pos L
  positivity

theorem geometricRatio_le_half (L : ℕ) : geometricRatio L ≤ 1 / 2 := by
  have h : (1 : ℚ) ≤ expansion L := by exact_mod_cast expansion_one_le L
  unfold geometricRatio
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  linarith

theorem width_pos (L n : ℕ) : 0 < width L n :=
  mul_pos (by norm_num) (pow_pos (geometricRatio_pos L) _)

theorem width_le (L n : ℕ) : width L n ≤ (1 / 1000000) * (1 / 2) ^ (n + 1) := by
  unfold width
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_left₀ (geometricRatio_pos L).le (geometricRatio_le_half L) _

theorem laplacianBound_nonneg (C L n : ℕ) : 0 ≤ laplacianBound C L n := by
  unfold laplacianBound
  positivity

theorem duration_pos (C L n : ℕ) : 0 < duration C L n := by
  unfold duration
  have h := laplacianBound_nonneg C L n
  positivity

theorem duration_le (C L n : ℕ) : duration C L n ≤ 1 / 100 := by
  unfold duration
  have h := laplacianBound_nonneg C L n
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  linarith

theorem diffusion_loss_small (C L n : ℕ) :
    2 * duration C L n * laplacianBound C L n < 1 / 16 := by
  have hD := laplacianBound_nonneg C L n
  have hd : (0 : ℚ) < 100 * (1 + laplacianBound C L n) := by positivity
  unfold duration
  rw [show 2 * (1 / (100 * (1 + laplacianBound C L n))) * laplacianBound C L n =
    (2 * laplacianBound C L n) / (100 * (1 + laplacianBound C L n)) by ring]
  apply (div_lt_iff₀ hd).mpr
  linarith

theorem heat_wait_long (C L n : ℕ) : 1 < 2 - 2 * duration C L n := by
  have h := duration_le C L n
  linarith

theorem massBound_small (L : ℕ) : 0 ≤ massBound L ∧ massBound L < 1 / 100000000000 := by
  have h₀ := geometricRatio_pos L
  have h₁ := geometricRatio_le_half L
  have hq : 0 ≤ geometricRatio L ^ 2 ∧ geometricRatio L ^ 2 ≤ 1 / 4 := by
    constructor
    · positivity
    · nlinarith
  have hd : 0 < 1 - geometricRatio L ^ 2 := by linarith
  constructor
  · unfold massBound
    positivity
  · unfold massBound
    apply (div_lt_iff₀ hd).mpr
    nlinarith [hq.1, hq.2]

theorem total_injected_mass (L : ℕ) :
    HasSum (fun n : ℕ => (4 : ℝ) * (width L n : ℝ) ^ 2) (massBound L : ℝ) := by
  let q : ℝ := (geometricRatio L : ℝ) ^ 2
  have hq : 0 ≤ q ∧ q ≤ 1 / 4 := by
    have h₀ : (0 : ℝ) < geometricRatio L := by exact_mod_cast geometricRatio_pos L
    have h₁ : (geometricRatio L : ℝ) ≤ 1 / 2 := by
      have h := (Rat.cast_le (K := ℝ)).mpr (geometricRatio_le_half L)
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
      exact h
    dsimp [q]
    constructor
    · positivity
    · nlinarith
  have hs := (hasSum_geometric_of_abs_lt_one (show |q| < 1 by
    rw [abs_of_nonneg hq.1]
    linarith)).mul_left ((4 : ℝ) * (1 / 1000000) ^ 2 * q)
  have he (n : ℕ) : (4 : ℝ) * (width L n : ℝ) ^ 2 =
      ((4 : ℝ) * (1 / 1000000) ^ 2 * q) * q ^ n := by
    have hp : ((geometricRatio L : ℝ) ^ (n + 1)) ^ 2 =
        ((geometricRatio L : ℝ) ^ 2) ^ n * (geometricRatio L : ℝ) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm (n + 1) 2, pow_mul, pow_succ]
    simp only [width, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_pow, mul_pow, hp, q]
    ring
  have hv : ((4 : ℝ) * (1 / 1000000) ^ 2 * q) * (1 - q)⁻¹ = (massBound L : ℝ) := by
    dsimp only [massBound, q]
    push_cast
    ring
  simpa only [← he, hv] using hs

end ForcedComputation.VelocityDetector

end OAI
