import OAI.NumberTheory.Ostmann.Characters.PivotProductPrior
import OAI.NumberTheory.Ostmann.Construction.TransferFrequencyRange

namespace OAI

/-! # Matching-fibre mass for the original mixed prime priors -/

namespace Ostmann
open scoped Classical BigOperators

/-- This applies simultaneously to the giant, broad-band, and deleted cell
marginals: only their already proved reciprocal-prime atom bounds are used. -/
theorem prime_tuple_prior_point_bound {n : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i)
    (x : Fin n → P) :
    productPrior μ x ≤ (∏ i, C i) * (∏ i, (x i : ℝ))⁻¹ := by
  have hi (i : Fin n) : μ i (x i) ≤ C i * (x i : ℝ)⁻¹ := by
    have hp : 0 < (x i : ℝ) := Nat.cast_pos.mpr (hP (x i) (x i).property).pos
    exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hbound i (x i))
  have h := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => hμ i (x i)) (fun i _ => hi i)
  simpa only [productPrior, Finset.prod_mul_distrib, Finset.prod_inv_distrib] using h

theorem prime_tuple_prior_product_mass {n : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i) (M : ℕ) :
    (∑ x : Fin n → P, if Function.Injective x ∧ (∏ i, (x i : ℕ)) = M then
      productPrior μ x else 0) ≤ (n.factorial : ℝ) * (∏ i, C i) * (M : ℝ)⁻¹ := by
  let S := (Finset.univ : Finset (Fin n → P)).filter
    (fun x : Fin n → P => Function.Injective x ∧ (∏ i, (x i : ℕ)) = M)
  have hc := card_distinct_prime_product_fiber P hP n M
  calc
    _ = ∑ x ∈ S, productPrior μ x := (Finset.sum_filter ..).symm
    _ ≤ ∑ _x ∈ S, (∏ i, C i) * (M : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have he : (∏ i, (x i : ℝ)) = (M : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp hx).2.2
      simpa only [he] using prime_tuple_prior_point_bound P hP μ C hμ hbound x
    _ = (S.card : ℝ) * ((∏ i, C i) * (M : ℝ)⁻¹) := by simp
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hc : (S.card : ℝ) ≤ n.factorial)
        (mul_nonneg (Finset.prod_nonneg (fun i _ => hC i)) (by positivity))

/-- A fixed product and a fixed root frequency incur no factor equal to the
number of frequencies. All original marginal probabilities are retained. -/
theorem prime_tuple_prior_frequency_mass {n : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (μ : Fin n → P → ℝ) (C : Fin n → ℝ)
    (hμ : ∀ i p, 0 ≤ μ i p) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (p : P), (p : ℝ) * μ i p ≤ C i) (V M : ℕ) (s : ℤ) :
    (∑ x : Fin n → P, ∑ v : transferFrequencyRange V,
      if Function.Injective x ∧ (∏ i, (x i : ℕ)) = M ∧ (v : ℤ) = s then
        productPrior μ x else 0) ≤
      (n.factorial : ℝ) * (∏ i, C i) * (M : ℝ)⁻¹ := by
  apply le_trans _ (prime_tuple_prior_product_mass P hP μ C hμ hC hbound M)
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : Function.Injective x ∧ (∏ i, (x i : ℕ)) = M
  · have he : (∑ v : transferFrequencyRange V, if (v : ℤ) = s then productPrior μ x else 0) =
        if s ∈ transferFrequencyRange V then productPrior μ x else 0 := by
      rw [Finset.sum_coe_sort (transferFrequencyRange V)
        (fun v : ℤ => if v = s then productPrior μ x else 0)]
      simp only [Finset.sum_ite_eq']
    have hi : (∑ v : transferFrequencyRange V,
        if Function.Injective x ∧ (∏ i, (x i : ℕ)) = M ∧ (v : ℤ) = s then
          productPrior μ x else 0) =
        ∑ v : transferFrequencyRange V, if (v : ℤ) = s then productPrior μ x else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [hx.1, hx.2, true_and]
    rw [hi, he, ite_eq_left hx]
    split_ifs
    · rfl
    · exact productPrior_nonneg μ hμ x
  · have hi : ∀ v : transferFrequencyRange V,
        ¬ (Function.Injective x ∧ (∏ i, (x i : ℕ)) = M ∧ (v : ℤ) = s) :=
      fun _ h => hx ⟨h.1, h.2.1⟩
    simp only [hi, ite_false, Finset.sum_const_zero, hx]
    exact le_rfl

end Ostmann

end OAI
