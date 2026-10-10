import Mathlib

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem shifted_power_le_threshold {x a τ : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    (hτ : 0 < τ) (k : ℕ) :
    (x + a) ^ (k - 2) ≤ (τ + a) ^ (k - 2) * (1 + (x / τ) ^ k) := by
  by_cases hxt : x ≤ τ
  · have hp := pow_le_pow_left₀ (add_nonneg hx ha) (add_le_add hxt le_rfl) (k - 2)
    have hR : 0 ≤ (x / τ) ^ k := pow_nonneg (div_nonneg hx hτ.le) k
    exact hp.trans (by nlinarith [mul_nonneg (pow_nonneg (by linarith : 0 ≤ τ + a) (k - 2)) hR])
  · have hR : 1 ≤ x / τ := (le_div_iff₀ hτ).mpr (by linarith)
    have hxa : x + a ≤ (τ + a) * (x / τ) := by
      have hax := mul_le_mul_of_nonneg_left hR ha
      have heq : τ * (x / τ) = x := by field_simp
      nlinarith
    have hp := pow_le_pow_left₀ (add_nonneg hx ha) hxa (k - 2)
    rw [mul_pow] at hp
    have hpk : (x / τ) ^ (k - 2) ≤ (x / τ) ^ k :=
      pow_le_pow_right₀ hR (Nat.sub_le k 2)
    have hnn : 0 ≤ (τ + a) ^ (k - 2) := pow_nonneg (by linarith) _
    calc
      _ ≤ (τ + a) ^ (k - 2) * (x / τ) ^ (k - 2) := hp
      _ ≤ (τ + a) ^ (k - 2) * (x / τ) ^ k := mul_le_mul_of_nonneg_left hpk hnn
      _ ≤ _ := by nlinarith

theorem weighted_shifted_power_le_threshold {α : Type*}
    (w H : α → ℝ) (hw : ∀ n, 0 ≤ w n) (hH : ∀ n, 0 ≤ H n)
    (hsw : Summable w) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) (k : ℕ)
    (hsH : Summable (fun n => w n * H n ^ k)) :
    (∑' n, w n * (H n + a) ^ (k - 2)) ≤
      (τ + a) ^ (k - 2) * ((∑' n, w n) + (∑' n, w n * H n ^ k) / τ ^ k) := by
  have hsR : Summable (fun n => (τ + a) ^ (k - 2) *
      (w n + w n * H n ^ k / τ ^ k)) := (hsw.add (hsH.div_const _)).mul_left _
  have hbound (n : α) : w n * (H n + a) ^ (k - 2) ≤
      (τ + a) ^ (k - 2) * (w n + w n * H n ^ k / τ ^ k) := by
    have h := mul_le_mul_of_nonneg_left (shifted_power_le_threshold (hH n) ha hτ k) (hw n)
    rw [div_pow] at h
    convert h using 1; ring
  have hsL : Summable (fun n => w n * (H n + a) ^ (k - 2)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hw n) (pow_nonneg (add_nonneg (hH n) ha) _))
      hbound hsR
  calc
    _ ≤ ∑' n, (τ + a) ^ (k - 2) * (w n + w n * H n ^ k / τ ^ k) :=
      hsL.tsum_le_tsum hbound hsR
    _ = _ := by rw [tsum_mul_left, hsw.tsum_add (hsH.div_const _), tsum_div_const]

end Ostmann.QuadraticCenter

end OAI
