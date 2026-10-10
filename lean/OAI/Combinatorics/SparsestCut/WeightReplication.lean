/-
Copyright (c) 2026 OpenAI. All rights reserved.
Authors: OpenAI
-/
import OAI.Combinatorics.SparsestCut.WeightReplacement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-!
# Replication of finite weights

Ceilings produce integer cluster sizes while giving one copy to every key of zero
weight. The resulting counting law satisfies the multiplicative and auxiliary-mass
estimates from Section 7 of OpenAI's *Constant-factor hardness of uniform sparsest cut*.
-/

open scoped BigOperators

namespace UniformSparsestCut.FiniteWeights

variable {ι : Type*} [Fintype ι]

noncomputable def copies (K : ℕ) (p : ℝ) : ℕ := if 0 < p then ⌈(K : ℝ) * p⌉₊ else 1

noncomputable def population (K : ℕ) (p : ι → ℝ) : ℕ := ∑ i, copies K (p i)

noncomputable def countingWeights (K : ℕ) (p : ι → ℝ) : ι → ℝ :=
  fun i => (copies K (p i) : ℝ) / population K p

omit [Fintype ι] in
theorem copies_zero (K : ℕ) : copies K 0 = 1 := by simp [copies]

omit [Fintype ι] in
theorem copies_pos (K : ℕ) (hK : 0 < K) (p : ℝ) : 0 < copies K p := by
  by_cases hp : 0 < p
  · simpa [copies, hp] using Nat.ceil_pos.mpr (mul_pos (Nat.cast_pos.mpr hK) hp)
  · simp [copies, hp]

omit [Fintype ι] in
theorem copies_lower (K : ℕ) {p : ℝ} (hp : 0 ≤ p) : (K : ℝ) * p ≤ copies K p := by
  by_cases hpos : 0 < p
  · simpa [copies, hpos] using Nat.le_ceil ((K : ℝ) * p)
  · have heq : p = 0 := le_antisymm (le_of_not_gt hpos) hp
    simp [heq, copies_zero]

omit [Fintype ι] in
theorem copies_upper (K : ℕ) {p : ℝ} (hp : 0 ≤ p) : (copies K p : ℝ) ≤ (K : ℝ) * p + 1 := by
  by_cases hpos : 0 < p
  · simpa [copies, hpos] using (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg K) hp)).le
  · have heq : p = 0 := le_antisymm (le_of_not_gt hpos) hp
    simp [heq, copies_zero]

theorem population_eq_total (K : ℕ) (p : ι → ℝ) :
    (population K p : ℝ) = total (fun i => (copies K (p i) : ℝ)) := by
  simp [population, total]

theorem population_bounds (K : ℕ) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hp₁ : total p = 1) :
    (K : ℝ) ≤ population K p ∧ (population K p : ℝ) ≤ K + Fintype.card ι := by
  constructor
  · calc
      (K : ℝ) = total (fun i => (K : ℝ) * p i) := by rw [total_smul, hp₁, mul_one]
      _ ≤ total (fun i => (copies K (p i) : ℝ)) := total_mono (fun i => copies_lower K (hp i))
      _ = _ := (population_eq_total K p).symm
  · calc
      (population K p : ℝ) = total (fun i => (copies K (p i) : ℝ)) := population_eq_total K p
      _ ≤ total (fun i => (K : ℝ) * p i + 1) := total_mono (fun i => copies_upper K (hp i))
      _ = _ := by rw [total_add, total_smul, hp₁, mul_one]; simp [total]

theorem population_pos (K : ℕ) (hK : 0 < K) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : total p = 1) : (0 : ℝ) < population K p :=
  lt_of_lt_of_le (Nat.cast_pos.mpr hK) (population_bounds K hp hp₁).1

theorem counting_nonneg (K : ℕ) (p : ι → ℝ) : ∀ i, 0 ≤ countingWeights K p i := by
  intro i
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem counting_total (K : ℕ) (hK : 0 < K) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : total p = 1) : total (countingWeights K p) = 1 := by
  change (∑ i, (copies K (p i) : ℝ) / population K p) = 1
  rw [← Finset.sum_div]
  change total (fun i => (copies K (p i) : ℝ)) / population K p = 1
  rw [← population_eq_total]
  exact div_self (ne_of_gt (population_pos K hK hp hp₁))

/-- On a key of positive weight, the counting law lies within a factor of two
of the original probability law. -/
theorem counting_bounds (K : ℕ) (hK : 0 < K) {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : total p = 1) (hKm : Fintype.card ι ≤ K)
    (hKp : ∀ i, 0 < p i → 1 ≤ (K : ℝ) * p i) (i : ι) (hpi : 0 < p i) :
    p i / 2 ≤ countingWeights K p i ∧ countingWeights K p i ≤ 2 * p i := by
  have hN₀ := population_pos K hK hp hp₁
  have hN := population_bounds K hp hp₁
  have hKm' : (Fintype.card ι : ℝ) ≤ K := by exact_mod_cast hKm
  have hN₂ : (population K p : ℝ) ≤ 2 * K := by linarith only [hN.2, hKm']
  have hlow := copies_lower K (hp i)
  have hupp := copies_upper K (hp i)
  have hmin := hKp i hpi
  constructor
  · apply (le_div_iff₀ hN₀).mpr
    have hn := mul_le_mul_of_nonneg_right hN₂ (hp i)
    nlinarith only [hn, hlow]
  · apply (div_le_iff₀ hN₀).mpr
    have hn := mul_le_mul_of_nonneg_right hN.1 (hp i)
    nlinarith only [hn, hmin, hupp]

/-- The total counting mass of auxiliary (zero-retained-demand) vertices. -/
theorem auxiliary_counting_bound (K : ℕ) (hK : 0 < K) {p : ι → ℝ} {κ : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hp₁ : total p = 1) (hκ : 0 < κ)
    (hKlarge : 4 * κ * Fintype.card ι ≤ K) :
    total (auxiliaryWeights (countingWeights K p) p) ≤ 1 / (4 * κ) := by
  classical
  have hN₀ := population_pos K hK hp hp₁
  have hN := (population_bounds K hp hp₁).1
  have ha : ∀ i, auxiliaryWeights (countingWeights K p) p i ≤ 1 / population K p := by
    intro i
    by_cases hi : p i = 0
    · simp [auxiliaryWeights, hi, countingWeights, copies_zero]
    · simp [auxiliaryWeights, hi, le_of_lt hN₀]
  have hasum : total (auxiliaryWeights (countingWeights K p) p) ≤
      (Fintype.card ι : ℝ) / population K p := by
    simpa [total, div_eq_mul_inv] using total_mono ha
  have hpop : 4 * κ * Fintype.card ι ≤ (population K p : ℝ) := hKlarge.trans hN
  have hbound : (Fintype.card ι : ℝ) / population K p ≤ 1 / (4 * κ) := by
    apply (div_le_div_iff₀ hN₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hκ)).mpr
    nlinarith only [hpop]
  exact hasum.trans hbound

end UniformSparsestCut.FiniteWeights

end OAI
