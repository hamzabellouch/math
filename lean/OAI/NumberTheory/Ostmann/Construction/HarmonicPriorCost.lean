import OAI.NumberTheory.Ostmann.Construction.HarmonicProductDomination

namespace OAI

/-! # The precise cost of replacing original bulk primes by unit residues -/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_prior_product_cost (n : ℕ) (S : TreeLeafIndex n → Finset ℕ)
    (J : TreeLeafIndex n → ℕ) (a C L : ℝ) (ha : 0 < a)
    (hmass : ∀ i, a ≤ ∑ p ∈ S i, (p : ℝ)⁻¹)
    (hJ : ∀ i, (J i : ℝ) ≤ Real.exp (C * L)) :
    (∏ i, (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) ≤
      Real.exp ((2 ^ n : ℕ) * (Real.log (3 / a) + C * L)) := by
  have he : (3 / a) * Real.exp (C * L) = Real.exp (Real.log (3 / a) + C * L) := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
  calc
    _ ≤ ∏ _i : TreeLeafIndex n, ((3 / a) * Real.exp (C * L)) := by
      apply Finset.prod_le_prod₀ (fun i _ => by positivity)
      intro i _
      have hi : (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ ≤ a⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le ha (hmass i)
      calc
        _ ≤ a⁻¹ * (3 * Real.exp (C * L)) :=
          mul_le_mul hi (mul_le_mul_of_nonneg_left (hJ i) (by norm_num))
            (by positivity) (by positivity)
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, card_treeLeafIndex, he, ← Real.exp_nat_mul]

/-- Once L is at least one, the prior loss has an absolute coefficient
per leaf, independent of the transfer depth. -/
theorem harmonic_prior_product_cost_linear (n : ℕ) (S : TreeLeafIndex n → Finset ℕ)
    (J : TreeLeafIndex n → ℕ) (a C L : ℝ) (ha : 0 < a) (hL : 1 ≤ L)
    (hmass : ∀ i, a ≤ ∑ p ∈ S i, (p : ℝ)⁻¹)
    (hJ : ∀ i, (J i : ℝ) ≤ Real.exp (C * L)) :
    (∏ i, (∑ p ∈ S i, (p : ℝ)⁻¹)⁻¹ * (3 * J i)) ≤
      Real.exp ((C + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L) := by
  apply (harmonic_prior_product_cost n S J a C L ha hmass hJ).trans
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (3 / a) ≤ max (Real.log (3 / a)) 0 * L := by
    have hh := mul_le_mul_of_nonneg_left hL (le_max_right (Real.log (3 / a)) 0)
    linarith [le_max_left (Real.log (3 / a)) 0]
  have hh := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ (2 ^ n : ℕ) by positivity)
  nlinarith

end Ostmann

end OAI
