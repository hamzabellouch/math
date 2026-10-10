import Mathlib.Algebra.Order.Floor.Ring
import OAI.NumberTheory.Ostmann.Characters.TreeComparisonError

namespace OAI

/-! # Uniform small parameters for the actual quartet tree error -/

namespace Ostmann

noncomputable def quartetTreeConstant (n : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 ^ (n + 2)) * (2 : ℝ) ^ (2 ^ n - 1) * 16384 *
    (128 : ℝ) ^ (2 ^ n - 1)

theorem quartetTreeConstant_pos (n : ℕ) : 0 < quartetTreeConstant n := by
  unfold quartetTreeConstant
  positivity

theorem quartetTree_error_le {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) * (quartetLocalMeanError p ε *
      (8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4) ^ (2 ^ n - 1))) ≤
    quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hu : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (by omega), Nat.cast_one]
  have hratio : (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) ≤ 2 := by
    rw [hu]
    exact (div_le_iff₀ (by linarith : 0 < (p : ℝ) - 1)).mpr (by linarith)
  have hr0 : 0 ≤ (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) := by positivity
  have hb : 8 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 ≤ 128 := by
    have h : ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 4 ≤ 16 := by
      calc
        _ ≤ (2 : ℝ) ^ 4 := pow_le_pow_left₀ hr0 hratio 4
        _ = 16 := by norm_num
    linarith
  calc
    _ ≤ (3 : ℝ) ^ (2 ^ (n + 2)) * ((2 : ℝ) ^ (2 ^ n - 1) *
        ((16384 * (ε ^ 2 + Real.sqrt (3 / (p : ℝ)))) * (128 : ℝ) ^ (2 ^ n - 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (quartetLocalMeanError_le hp ε hε hε1)
        (pow_le_pow_left₀ (by positivity) hb _) (by positivity) (by positivity)
    _ = _ := by unfold quartetTreeConstant; ring

theorem exists_quartet_small_parameters (K δ : ℝ) (hK : 0 < K) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ p : ℕ, N ≤ p → K * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) ≤ δ ^ 2 := by
  let t := min 1 (δ ^ 2 / (2 * K))
  have ht : 0 < t := lt_min (by norm_num) (div_pos (sq_pos_of_pos hδ) (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htδ : 2 * K * t ≤ δ ^ 2 := by
    have htl : t ≤ δ ^ 2 / (2 * K) := min_le_right _ _
    have h := (le_div_iff₀ (by positivity : 0 < 2 * K)).mp htl
    nlinarith
  refine ⟨Real.sqrt t, Real.sqrt_pos.2 ht, ?_, max 3 ⌈3 / t ^ 2⌉₊, le_max_left _ _, ?_⟩
  · exact (Real.sqrt_le_one).mpr ht1
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (le_max_left 3 ⌈3 / t ^ 2⌉₊).trans hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hpt : 3 / t ^ 2 ≤ (p : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hp))
    have hdiv : 3 / (p : ℝ) ≤ t ^ 2 := by
      apply (div_le_iff₀ hp0).mpr
      have h := (div_le_iff₀ (sq_pos_of_pos ht)).mp hpt
      nlinarith
    have hsqrt : Real.sqrt (3 / (p : ℝ)) ≤ t := (Real.sqrt_le_iff).mpr ⟨ht.le, hdiv⟩
    rw [Real.sq_sqrt ht.le]
    nlinarith

end Ostmann

end OAI
