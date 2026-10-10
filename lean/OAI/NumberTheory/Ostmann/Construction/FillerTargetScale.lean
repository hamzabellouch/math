import OAI.NumberTheory.Ostmann.Characters.CharacterTargetGaps

namespace OAI

/-! # The filler target completing the prescribed total product -/

namespace Ostmann

open scoped BigOperators

noncomputable def fillerTarget (k : ℕ) (τ Δ₀ J A T : ℝ) : ℝ :=
  (1000 * (4 : ℝ) ^ k * τ + Δ₀) / 2 - J - (T + A)

theorem fillerTarget_bounds (k : ℕ) (τ Δ₀ J A T : ℝ) (hτ : 0 < τ)
    (hΔ₀ : 0 ≤ Δ₀ ∧ Δ₀ ≤ τ / 4) (hJ : 0 ≤ J ∧ J ≤ 4 * τ)
    (hA : 0 ≤ A ∧ A ≤ 4 * k * τ) (hT : 0 ≤ T ∧ T ≤ 8 * (4 : ℝ) ^ k * τ) :
    (2 : ℝ) ^ k * τ ≤ fillerTarget k τ Δ₀ J A T ∧
      fillerTarget k τ Δ₀ J A T ≤ 501 * (4 : ℝ) ^ k * τ := by
  have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h24 : (2 : ℝ) ^ k ≤ 4 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hk4 := hk2.trans h24
  have h41 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hτ4 := mul_le_mul_of_nonneg_right h41 hτ.le
  have hA4 := mul_le_mul_of_nonneg_right hk4 hτ.le
  have h24τ := mul_le_mul_of_nonneg_right h24 hτ.le
  dsimp [fillerTarget]
  constructor <;> nlinarith [hΔ₀.1, hΔ₀.2, hJ.1, hJ.2, hA.1, hA.2, hT.1, hT.2]

theorem fillerTarget_balance (k : ℕ) (τ Δ₀ J A T : ℝ) :
    2 * (J + T + A + fillerTarget k τ Δ₀ J A T) = 1000 * (4 : ℝ) ^ k * τ + Δ₀ := by
  unfold fillerTarget
  ring

theorem constructed_fillerTarget_bounds (k : ℕ) (hk : 0 < k) (J τ Δ₀ : ℝ)
    (a Δ : Fin k → ℝ) (hτ : 0 < τ) (hJlo : τ / 2 ≤ J) (hJhi : J ≤ 4 * τ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 4 * τ)
    (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ (2 : ℝ) ^ i.val * τ / 4)
    (hΔ₀ : 0 ≤ Δ₀ ∧ Δ₀ ≤ τ / 4) :
    let F := fillerTarget k τ Δ₀ J (∑ i, a i) (pivotTargets k J a Δ).sum
    (2 : ℝ) ^ k * τ ≤ F ∧ F ≤ 501 * (4 : ℝ) ^ k * τ := by
  have htargets := pivotTargets_bounds k hk J τ a Δ hτ hJlo hJhi ha hΔ
  have hA : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => (ha i).1)
  have hAup : (∑ i, a i) ≤ 4 * k * τ := by
    calc
      _ ≤ ∑ _i : Fin k, 4 * τ := Finset.sum_le_sum (fun i _ => (ha i).2)
      _ = _ := by simp; ring
  have hT : 0 ≤ (pivotTargets k J a Δ).sum := by
    apply List.sum_nonneg
    intro T hT
    exact (by positivity : 0 ≤ (2 : ℝ) ^ (k - 1) * τ / 4).trans (htargets.2.2 T hT).1
  exact fillerTarget_bounds k τ Δ₀ J _ _ hτ hΔ₀ ⟨by linarith, hJhi⟩ ⟨hA, hAup⟩ ⟨hT, htargets.2.1⟩

end Ostmann

end OAI
