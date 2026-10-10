import OAI.Combinatorics.ContingencyTables.Sampling.Padding
import OAI.Combinatorics.ContingencyTables.Sampling.ResidualMixture
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Parameter arithmetic for the samplers

The manuscript's padding and rare tabulation estimates give explicit
inequalities for successful unpadding and expected correction cost.
-/

namespace ContingencyTables

open scoped BigOperators

private theorem padding_error_le_half (d s : ℕ) (hd : 14 ≤ d) (hs : s ≤ d) :
    (s : ℝ) * (4 * (d : ℝ) ^ 12 * (d : ℝ) ^ 3 / (d : ℝ) ^ 20) ≤ 1 / 2 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd₁₄ : (14 : ℝ) ≤ d := by exact_mod_cast hd
  have hs' : (s : ℝ) ≤ d := by exact_mod_cast hs
  have hfour : (8 : ℝ) ≤ (d : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 14) hd₁₄ 4
    norm_num at h
    linarith
  have htwenty : (d : ℝ) ^ 20 = (d : ℝ) ^ 16 * (d : ℝ) ^ 4 := by ring
  have hpow : (0 : ℝ) ≤ (d : ℝ) ^ 16 := by positivity
  have hlarge := mul_le_mul_of_nonneg_left hfour hpow
  have hnum : 8 * (s : ℝ) * (d : ℝ) ^ 12 * (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 20 := by
    calc
      _ ≤ 8 * (d : ℝ) * (d : ℝ) ^ 12 * (d : ℝ) ^ 3 := by gcongr
      _ = 8 * (d : ℝ) ^ 16 := by ring
      _ ≤ (d : ℝ) ^ 20 := by rw [htwenty]; linarith
  rw [← mul_div_assoc, div_le_iff₀ (pow_pos hd₀ 20)]
  nlinarith

/-- For the actual choices `L=d¹²`, `U=d²⁰`, the uniform padded table
unpads successfully with probability at least one half. -/
theorem padding_success_half {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (K : Finset (I × J)) (d : ℕ) (hd : 14 ≤ d)
    (hrows : Fintype.card I ≤ d) (hcols : Fintype.card J ≤ d)
    (hK : K.card ≤ d) (hrow : ∀ p ∈ K, d ^ 20 ≤ r p.1)
    (hcol : ∀ p ∈ K, d ^ 20 ≤ c p.2) :
    (1 / 2 : ℝ) ≤ (Fintype.card (Table r c) : ℝ) /
      Fintype.card (Table (paddedRows r (largePadding K (d ^ 12)))
        (paddedColumns c (largePadding K (d ^ 12)))) := by
  have hd₀ : 0 < d := by omega
  have hU : 4 * d ≤ d ^ 20 := by
    have hd₄ : 4 ≤ d := by omega
    have hpow : d ≤ d ^ 19 := Nat.le_self_pow (by decide) d
    calc
      4 * d ≤ d * d ^ 19 := Nat.mul_le_mul hd₄ hpow
      _ = d ^ 20 := by ring
  have hL : 2 * d ^ 12 ≤ d ^ 20 := by
    have hpow : d ≤ d ^ 8 := Nat.le_self_pow (by decide) d
    have hd₂ : 2 ≤ d ^ 8 := by omega
    calc
      2 * d ^ 12 ≤ d ^ 8 * d ^ 12 := Nat.mul_le_mul_right _ hd₂
      _ = d ^ 20 := by ring
  have h := padding_success_fraction r c htotal K (d ^ 12) (d ^ 20) d
    hd₀ hrows hcols hrow hcol hU hL
  have he := padding_error_le_half d K.card hd hK
  push_cast at h
  linarith

/-- The exponentially costly exact tabulation branch has exponentially
smaller probability for the manuscript's `D=d⁶b²`. -/
theorem rare_tabulation_exponent (d b : ℕ) (hd : 14 ≤ d) (_hb : 1 ≤ b) :
    500 * d * b ≤ d ^ 6 * b ^ 2 := by
  have hfive : 500 ≤ d ^ 5 := by
    have h := Nat.pow_le_pow_left hd 5
    norm_num at h
    omega
  have hb₂ : b ≤ b ^ 2 := Nat.le_self_pow (by decide) b
  calc
    500 * d * b ≤ d ^ 5 * d * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_right d hfive)
    _ = d ^ 6 * b := by ring
    _ ≤ d ^ 6 * b ^ 2 := Nat.mul_le_mul_left _ hb₂

theorem rare_tabulation_cost (d b : ℕ) (hd : 14 ≤ d) (hb : 1 ≤ b) :
    (2 : ℚ) ^ (500 * d * b) / (2 : ℚ) ^ (d ^ 6 * b ^ 2) ≤ 1 := by
  apply (div_le_one (by positivity)).mpr
  exact pow_le_pow_right₀ (by norm_num) (rare_tabulation_exponent d b hd hb)

end ContingencyTables

end OAI
