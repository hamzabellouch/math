import OAI.NumberTheory.Ostmann.Construction.PrimeRestorationDifference
import OAI.NumberTheory.Ostmann.Arithmetic.BulkDeletionCost

namespace OAI

/-! # Returning the conditional bulk law to its initial harmonic prior -/

namespace Ostmann
open scoped Classical BigOperators

/-- Deleting primes after fixing nonbulk coordinates does not change the
initial law silently. Its signed mean is controlled by the conditional mean
plus the exact restored-mass cost, with the latter's original normalizer. -/
theorem initial_prime_prior_bound {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hnew : ∀ j, 0 < ∑ q ∈ S j \ D j, (q : ℝ)⁻¹)
    (F : (J → P) → ℂ) (B : ℝ) (hF : ∀ x, ‖F x‖ ≤ B) :
    let Z := fun j => (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹
    ‖∑ x, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) * F x‖ ≤
      ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x‖ +
        B * ((∏ j, (1 + Z j * ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) := by
  intro Z
  let oldMass := fun j => ∑ q ∈ S j, (q : ℝ)⁻¹
  let newMass := fun j => ∑ q ∈ S j \ D j, (q : ℝ)⁻¹
  let ρ := fun j => newMass j / oldMass j
  let restored := fun j (q : P) => if (q : ℕ) ∈ S j then Z j * (q : ℝ)⁻¹ else 0
  have hmass (j) : newMass j ≤ oldMass j :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intros; positivity)
  have hold (j) : 0 < oldMass j := (hnew j).trans_le (hmass j)
  have hρ0 (j) : 0 ≤ ρ j := div_nonneg (hnew j).le (hold j).le
  have hρ1 (j) : ρ j ≤ 1 := (div_le_one (hold j)).mpr (hmass j)
  have hprior (j) (q : P) : primeSubsetPrior P (S j) q = ρ j * restored j q := by
    by_cases hq : (q : ℕ) ∈ S j
    · simp only [primeSubsetPrior, hq, ite_true, restored]
      dsimp only [ρ, oldMass, newMass, Z]
      field_simp [(hnew j).ne', (hold j).ne']
    · simp only [primeSubsetPrior, hq, ite_false, restored, mul_zero]
  have heq :
      (∑ x : J → P, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) * F x) =
      ((∏ j, ρ j : ℝ) : ℂ) * ∑ x : J → P, ((∏ j, restored j (x j) : ℝ) : ℂ) * F x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [hprior]
    rw [Finset.prod_mul_distrib, Complex.ofReal_mul, mul_assoc]
  have hρprod : (∏ j, ρ j) ≤ 1 := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod₀ (fun j (_ : j ∈ (Finset.univ : Finset J)) => hρ0 j) (fun j _ => hρ1 j)
  have hscale : ‖∑ x : J → P, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) * F x‖ ≤
      ‖∑ x : J → P, ((∏ j, restored j (x j) : ℝ) : ℂ) * F x‖ := by
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun j _ => hρ0 j)]
    exact mul_le_of_le_one_left (norm_nonneg _) hρprod
  have hd := original_prime_restoration_difference P S D hSP (fun j => (hnew j).ne') F B hF
  dsimp only at hd
  have ht := norm_le_norm_add_norm_sub
    (∑ x : J → P, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x)
    (∑ x : J → P, ((∏ j, restored j (x j) : ℝ) : ℂ) * F x)
  exact hscale.trans (ht.trans (add_le_add le_rfl hd))

/-- The extra return to the initial law has the same elementary deleted
atomic-mass cost; it introduces no new prime-distribution assumption. -/
theorem initial_prime_prior_deleted_cost {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hnew : ∀ j, 0 < ∑ q ∈ S j \ D j, (q : ℝ)⁻¹)
    (F : (J → P) → ℂ) (B H T K : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B)
    (hZ : ∀ j, (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hD : ∀ j, ((D j).card : ℝ) ≤ K)
    (hlow : ∀ j q, q ∈ S j → Real.exp T ≤ (q : ℝ))
    (hsmall : (Fintype.card J : ℝ) * K * Real.exp (H - T) ≤ 1) :
    ‖∑ x, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) * F x‖ ≤
      ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x‖ +
        B * (2 * (Fintype.card J : ℝ) * K * Real.exp (H - T)) := by
  apply (initial_prime_prior_bound P S D hSP hnew F B hF).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hB
  exact bulk_deleted_product_cost S D _ H T K
    (fun j => inv_nonneg.mpr (hnew j).le) hZ hD hlow hsmall

/-- Scalar error assembly is separate from the original observable, avoiding
repeated elaboration of its full arithmetic expression. -/
theorem initial_prime_prior_three_errors {J : Type*} [Fintype J]
    (P : Finset ℕ) (S D : J → Finset ℕ) (hSP : ∀ j, S j ⊆ P)
    (hnew : ∀ j, 0 < ∑ q ∈ S j \ D j, (q : ℝ)⁻¹)
    (F : (J → P) → ℂ) (B main error tail : ℝ) (hF : ∀ x, ‖F x‖ ≤ B)
    (hmean : ‖∑ x, ((∏ j, primeSubsetPrior P (S j \ D j) (x j) : ℝ) : ℂ) * F x‖ ≤
      main + error + tail)
    (herror : B * ((∏ j, (1 + (∑ q ∈ S j \ D j, (q : ℝ)⁻¹)⁻¹ *
      ∑ q ∈ S j ∩ D j, (q : ℝ)⁻¹)) - 1) ≤ tail) :
    ‖∑ x, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) * F x‖ ≤
      main + error + 2 * tail := by
  apply (initial_prime_prior_bound P S D hSP hnew F B hF).trans
  exact (add_le_add hmean herror).trans_eq (by ring)

end Ostmann

end OAI
