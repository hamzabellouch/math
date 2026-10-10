import OAI.NumberTheory.Ostmann.Arithmetic.RestoredPrimeCellExpansion
import OAI.NumberTheory.Ostmann.Arithmetic.IndexedBulkDistinctness

namespace OAI

/-! # Deletion and collision errors for arbitrary signed prime observables -/

namespace Ostmann
open scoped Classical BigOperators

/-- Monotone restoration costs exactly the excess mass of the product law.
The observable can retain residue classes and every other arithmetic factor. -/
theorem finite_product_restoration_difference {J A : Type*} [Fintype J] [Fintype A]
    (μ ν : J → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hle : ∀ j a, μ j a ≤ ν j a)
    (hmass : ∀ j, ∑ a, μ j a = 1) (F : (J → A) → ℂ)
    (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖(∑ x, ((∏ j, μ j (x j) : ℝ) : ℂ) * F x) -
      ∑ x, ((∏ j, ν j (x j) : ℝ) : ℂ) * F x‖ ≤
      B * ((∏ j, ∑ a, ν j a) - 1) := by
  have hp (x : J → A) : (∏ j, μ j (x j)) ≤ ∏ j, ν j (x j) :=
    Finset.prod_le_prod₀ (fun j _ => hμ j (x j)) (fun j _ => hle j (x j))
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x : J → A, B * ((∏ j, ν j (x j)) - ∏ j, μ j (x j)) := by
      apply norm_sum_le_of_le
      intro x _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hp x))]
      exact (mul_le_mul_of_nonneg_left (hF x) (sub_nonneg.mpr (hp x))).trans_eq
        (mul_comm _ _)
    _ = B * ((∏ j, ∑ a, ν j a) - 1) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib,
        ← Fintype.prod_sum, ← Fintype.prod_sum]
      simp only [hmass, Finset.prod_const_one]

/-- Restoring deleted atoms retains the old normalization. -/
theorem original_prime_restoration_difference {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hS : ∀ j, (∑ p ∈ S j \ D j, (p : ℝ)⁻¹) ≠ 0)
    (F : (J → P) → ℂ) (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    ‖(∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x) -
      ∑ x, ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) * F x‖ ≤
      B * ((∏ j, (1 + Z j * ∑ p ∈ S j ∩ D j, (p : ℝ)⁻¹)) - 1) := by
  dsimp only
  let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
  let ν := fun j (p : P) => if (p : ℕ) ∈ S j then Z j * (p : ℝ)⁻¹ else 0
  have hle (j : J) (p : P) : primeSubsetPrior P (S j \ D j) p ≤ ν j p := by
    by_cases hp : (p : ℕ) ∈ S j \ D j
    · have hps := (Finset.mem_sdiff.mp hp).1
      simp only [primeSubsetPrior, hp, hps, ite_true, ν, Z, div_eq_mul_inv]
      exact le_of_eq (mul_comm _ _)
    · simp only [primeSubsetPrior, hp, ite_false]
      dsimp only [ν]
      split_ifs <;> positivity
  have hm (j : J) : (∑ p : P, ν j p) =
      1 + Z j * ∑ p ∈ S j ∩ D j, (p : ℝ)⁻¹ := by
    have he : (∑ p : P, ν j p) = Z j * ∑ p ∈ S j, (p : ℝ)⁻¹ := by
      dsimp only [ν]
      rw [Finset.sum_coe_sort P (fun p : ℕ => if p ∈ S j then Z j * (p : ℝ)⁻¹ else 0)]
      rw [← Finset.sum_filter]
      have hfilter : P.filter (· ∈ S j) = S j := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun hp => ⟨hSP j hp, hp⟩⟩
      rw [hfilter, Finset.mul_sum]
    rw [he, ← Finset.sum_inter_add_sum_sdiff (S j) (D j) (fun p : ℕ => (p : ℝ)⁻¹), mul_add]
    have hz : Z j * (∑ p ∈ S j \ D j, (p : ℝ)⁻¹) = 1 := inv_mul_cancel₀ (hS j)
    rw [hz, add_comm]
  have h := finite_product_restoration_difference
    (fun j => primeSubsetPrior P (S j \ D j)) ν
    (fun j p => primeSubsetPrior_nonneg P (S j \ D j) p) hle
    (fun j => primeSubsetPrior_mass P (S j \ D j) (Finset.sdiff_subset.trans (hSP j)) (hS j)) F B hF
  simpa only [hm] using h

private theorem norm_le_from_restoration {x y z : ℂ} {A B C : ℝ}
    (hx : ‖x - y‖ ≤ B) (hy : ‖y - z‖ ≤ C) (hz : ‖z‖ ≤ A) :
    ‖x‖ ≤ A + B + C := by
  have hxy : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub y x
  have hyz : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub z y
  linarith

/-- The original injective expectation is bounded by the restored expectation,
with separate collision and deleted-atom costs. -/
theorem original_bulk_collision_restoration_bound {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hS : ∀ j, (∑ p ∈ S j \ D j, (p : ℝ)⁻¹) ≠ 0)
    (H T : ℝ) (hmass : ∀ j, (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hlow : ∀ j p, p ∈ S j \ D j → Real.exp T ≤ (p : ℝ))
    (F : (J → P) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B)
    (M : ℝ)
    (hmain : ‖∑ x, ((∏ j, (if (x j : ℕ) ∈ S j then
      (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹ * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) * F x‖ ≤ M) :
    ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) *
      (if Function.Injective x then F x else 0)‖ ≤
      M + B * (Fintype.card J : ℝ) ^ 2 * Real.exp (H - T) +
        B * ((∏ j, (1 + (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹ *
          ∑ p ∈ S j ∩ D j, (p : ℝ)⁻¹)) - 1) := by
  have hc := original_bulk_distinctness_removal_indexed P (fun j => S j \ D j)
    (fun j => Finset.sdiff_subset.trans (hSP j)) hS H T hmass hlow F B hB hF
  have hd := original_prime_restoration_difference P S D hSP hS F B hF
  dsimp only at hd
  have h := norm_le_from_restoration hc hd hmain
  simpa only [finite_univ_canonical] using h

end Ostmann

end OAI
