import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # Polynomial upper growth supplies arbitrarily large tripling scales

Only an upper polynomial estimate is needed for the Haar averaging step:
there are arbitrarily large radii where tripling the radius has bounded
volume ratio. No full volume asymptotic or lower polynomial estimate is used.
-/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A positive sequence tending to zero cannot increase at every step. -/
theorem exists_adjacent_nonincrease_of_tendsto_zero
    (a : ℕ → ℝ) (ha : 0 < a 0) (hlim : Tendsto a atTop (𝓝 0)) :
    ∃ n, a (n + 1) ≤ a n := by
  by_contra! h
  have hmono : Monotone a := monotone_nat_of_le_succ (fun n => (h n).le)
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds ha)).exists
  exact (hmono (Nat.zero_le n)).not_gt hn

/-- An exponential upper bound forces one adjacent growth ratio below any
fixed larger exponential rate. -/
theorem exists_geometric_growth_ratio
    (v : ℕ → ℝ) {C B : ℝ} (hB : 0 < B)
    (hv : ∀ n, 0 ≤ v n) (hv0 : 0 < v 0)
    (hbound : ∀ n, v n ≤ C * B ^ n) :
    ∃ n, v (n + 1) ≤ (2 * B) * v n := by
  let a := fun n => v n / (2 * B) ^ n
  have ha (n : ℕ) : 0 ≤ a n := div_nonneg (hv n) (pow_pos (by positivity) n).le
  have hab (n : ℕ) : a n ≤ C * (1 / 2 : ℝ) ^ n := by
    dsimp only [a]
    calc
      v n / (2 * B) ^ n ≤ (C * B ^ n) / (2 * B) ^ n :=
        div_le_div_of_nonneg_right (hbound n) (pow_pos (by positivity) n).le
      _ = C * (B / (2 * B)) ^ n := by rw [div_pow]; ring
      _ = C * (1 / 2 : ℝ) ^ n := by congr 2; field_simp
  have hgeo : Tendsto (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hlim : Tendsto a atTop (𝓝 0) := squeeze_zero ha hab hgeo
  obtain ⟨n, hn⟩ := exists_adjacent_nonincrease_of_tendsto_zero a (by simpa [a] using hv0) hlim
  have hden : 0 < (2 * B) ^ (n + 1) := pow_pos (by positivity) _
  have hp : (2 * B) ^ (n + 1) = (2 * B) ^ n * (2 * B) := pow_succ _ _
  have hh := (div_le_iff₀ hden).mp hn
  dsimp only [a] at hh
  rw [hp] at hh
  have he : (v n / (2 * B) ^ n) * ((2 * B) ^ n * (2 * B)) = (2 * B) * v n := by
    field_simp
  rw [he] at hh
  exact ⟨n, hh⟩

/-- Positive polynomial volume growth admits a tripling estimate at some
radius above every prescribed threshold. -/
theorem polynomial_tripling_at_arbitrarily_large_radii
    (v : ℝ → ℝ) {C : ℝ} (d : ℕ)
    (hv : ∀ r, 1 ≤ r → 0 < v r)
    (hbound : ∀ r, 1 ≤ r → v r ≤ C * r ^ d) :
    ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧ 1 ≤ T ∧ v (3 * T) ≤ (2 * (3 : ℝ) ^ d) * v T := by
  intro R
  let r := max R 1
  have hr : 1 ≤ r := le_max_right _ _
  have hn (n : ℕ) : 1 ≤ (3 : ℝ) ^ n * r := by
    have hp : 1 ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  obtain ⟨n, hratio⟩ := exists_geometric_growth_ratio (fun n => v ((3 : ℝ) ^ n * r))
    (C := C * r ^ d) (B := (3 : ℝ) ^ d) (by positivity)
    (fun n => (hv _ (hn n)).le) (by simpa using hv r hr) (by
      intro n
      calc
        v ((3 : ℝ) ^ n * r) ≤ C * ((3 : ℝ) ^ n * r) ^ d := hbound _ (hn n)
        _ = (C * r ^ d) * ((3 : ℝ) ^ d) ^ n := by rw [mul_pow, ← pow_mul, Nat.mul_comm n d, pow_mul]; ring)
  refine ⟨(3 : ℝ) ^ n * r, (le_max_left R 1).trans (by nlinarith [hn n, one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) (n := n)]), hn n, ?_⟩
  simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hratio

end PolycyclicRecognition

end OAI
