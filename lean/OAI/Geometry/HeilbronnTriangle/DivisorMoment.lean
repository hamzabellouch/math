import Mathlib

namespace OAI


open scoped BigOperators

namespace Problem355.DivisorMoment

theorem weighted_power_moment_le_geom_sum
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
    (B ρ : ℝ) (k : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hB : 0 ≤ B)
    (hb : ∀ ω, b ω ≤ k)
    (htail : ∀ j, j ≤ k →
      (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j) :
    (∑ ω, p ω * B ^ b ω) ≤
      ∑ j ∈ Finset.range (k + 1), (B * ρ) ^ j := by
  classical
  calc
    (∑ ω, p ω * B ^ b ω) ≤
        ∑ ω, p ω * (∑ j ∈ Finset.range (k + 1),
          if j ≤ b ω then B ^ j else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (hp ω)
      have hsingle := Finset.single_le_sum
        (s := Finset.range (k + 1))
        (f := fun j => if j ≤ b ω then B ^ j else 0)
        (fun j _ => by split_ifs <;> positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (hb ω)))
      simpa using hsingle
    _ = ∑ j ∈ Finset.range (k + 1),
        B ^ j * (∑ ω, if j ≤ b ω then p ω else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp [mul_comm]
    _ ≤ ∑ j ∈ Finset.range (k + 1), B ^ j * ρ ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (htail j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
        (pow_nonneg hB j)
    _ = ∑ j ∈ Finset.range (k + 1), (B * ρ) ^ j := by
      simp_rw [mul_pow]

theorem weighted_power_moment_le_inv
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
    (B ρ : ℝ) (k : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hb : ∀ ω, b ω ≤ k)
    (htail : ∀ j, j ≤ k →
      (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
    (hsmall : B * ρ < 1) :
    (∑ ω, p ω * B ^ b ω) ≤ 1 / (1 - B * ρ) := by
  apply (weighted_power_moment_le_geom_sum p b B ρ k hp hB hb htail).trans
  simpa using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := k + 1)
      (mul_nonneg hB hρ) hsmall)

theorem normalized_power_moment_le_inv
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
    (B ρ : ℝ) (k : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hmass : ∑ ω, p ω = 1)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hb : ∀ ω, b ω ≤ k)
    (htail : ∀ j, 1 ≤ j → j ≤ k →
      (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
    (hsmall : B * ρ < 1) :
    (∑ ω, p ω * B ^ b ω) ≤ 1 / (1 - B * ρ) := by
  apply weighted_power_moment_le_inv p b B ρ k hp hB hρ hb _ hsmall
  intro j hj
  rcases j with _ | j
  · simp [hmass]
  · exact htail (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) hj

theorem normalized_power_moment_le_two
    {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (b : Ω → ℕ)
    (B ρ : ℝ) (k : ℕ)
    (hp : ∀ ω, 0 ≤ p ω) (hmass : ∑ ω, p ω = 1)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hb : ∀ ω, b ω ≤ k)
    (htail : ∀ j, 1 ≤ j → j ≤ k →
      (∑ ω, if j ≤ b ω then p ω else 0) ≤ ρ ^ j)
    (hsmall : B * ρ ≤ 1 / 2) :
    (∑ ω, p ω * B ^ b ω) ≤ 2 := by
  have heta : B * ρ < 1 := lt_of_le_of_lt hsmall (by norm_num)
  apply (normalized_power_moment_le_inv p b B ρ k hp hmass hB hρ hb
    htail heta).trans
  apply (div_le_iff₀ (sub_pos.mpr heta)).mpr
  nlinarith

theorem exceptional_weighted_moment_le
    {Λ : Type*} [Fintype Λ] (q M : Λ → ℝ) (E : Λ → Prop)
    [DecidablePred E] (C δ : ℝ)
    (hq : ∀ ℓ, 0 ≤ q ℓ) (hC : 0 ≤ C) (hM : ∀ ℓ, M ℓ ≤ C)
    (hE : (∑ ℓ, if E ℓ then q ℓ else 0) ≤ δ) :
    (∑ ℓ, if E ℓ then q ℓ * M ℓ else 0) ≤ C * δ := by
  calc
    (∑ ℓ, if E ℓ then q ℓ * M ℓ else 0) ≤
        ∑ ℓ, if E ℓ then q ℓ * C else 0 := by
      apply Finset.sum_le_sum
      intro ℓ _
      split_ifs
      · exact mul_le_mul_of_nonneg_left (hM ℓ) (hq ℓ)
      · exact le_rfl
    _ = C * (∑ ℓ, if E ℓ then q ℓ else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      split_ifs <;> simp [mul_comm]
    _ ≤ C * δ := mul_le_mul_of_nonneg_left hE hC

theorem exceptional_divisor_moment_le
    {Λ Ω : Type*} [Fintype Λ] [Fintype Ω]
    (q : Λ → ℝ) (p : Λ → Ω → ℝ) (b : Λ → Ω → ℕ)
    (E : Λ → Prop) [DecidablePred E] (B ρ δ : ℝ) (k : ℕ)
    (hq : ∀ ℓ, 0 ≤ q ℓ) (hp : ∀ ℓ ω, 0 ≤ p ℓ ω)
    (hmass : ∀ ℓ, ∑ ω, p ℓ ω = 1)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hb : ∀ ℓ ω, b ℓ ω ≤ k)
    (htail : ∀ ℓ j, 1 ≤ j → j ≤ k →
      (∑ ω, if j ≤ b ℓ ω then p ℓ ω else 0) ≤ ρ ^ j)
    (hsmall : B * ρ ≤ 1 / 2)
    (hE : (∑ ℓ, if E ℓ then q ℓ else 0) ≤ δ) :
    (∑ ℓ, if E ℓ then q ℓ * (∑ ω, p ℓ ω * B ^ b ℓ ω) else 0)
      ≤ 2 * δ := by
  apply exceptional_weighted_moment_le q
    (fun ℓ => ∑ ω, p ℓ ω * B ^ b ℓ ω) E 2 δ hq (by norm_num) _ hE
  intro ℓ
  exact normalized_power_moment_le_two (p ℓ) (b ℓ) B ρ k
    (hp ℓ) (hmass ℓ) hB hρ (hb ℓ) (htail ℓ) hsmall

end Problem355.DivisorMoment

end OAI
