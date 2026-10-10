import OAI.NumberTheory.CubicMoment.Estimates.BoundedPrimeTuples

namespace OAI

/-! Bounded ordered prime-factor expansion of the rough remainder in
the large-R branch. Every tuple has its literal primary product. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma ordered_primary_factor_product {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    (e : Fin (primaryPrimeFactors n).card ≃ primaryPrimeFactors n) :
    (∏ i, (e i:Eisenstein)) = n := by
  calc
    _ = ∏ p ∈ primaryPrimeFactors n, p :=
      (e.prod_comp (fun p : primaryPrimeFactors n => (p:Eisenstein))).trans
        (Finset.prod_coe_sort (primaryPrimeFactors n) (fun p : Eisenstein => p))
    _ = n := primaryPrimeFactors_prod hn hs

lemma roughProduct_ordered_primary_factors (ψ : ℝ → ℝ) (w : ℝ) (n : Eisenstein) :
    (roughProduct ψ w n:ℂ) = ((primaryPrimeFactors n).card.factorial:ℂ)⁻¹*
      ∑ e : Fin (primaryPrimeFactors n).card ≃ primaryPrimeFactors n,
        ∏ i, (1-(ψ (norm (e i)/w):ℂ)) := by
  rw [ordered_subset_product (primaryPrimeFactors n)
    (fun p : Eisenstein => 1-(ψ (norm p/w):ℂ)),roughProduct_primary_factors]
  push_cast
  rfl

lemma roughProduct_nonzero_prime_bound {ψ : ℝ → ℝ}
    (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    {w : ℝ} (hw : 0 < w) {n : Eisenstein} (hn : primary n)
    (hne : roughProduct ψ w n ≠ 0) {p : Eisenstein} (hp : p ∈ primaryPrimeFactors n) :
    w < norm p := by
  rw [roughProduct_primary_factors] at hne
  have hpne := (Finset.prod_ne_zero_iff.mp hne) p hp
  by_contra h
  apply hpne
  rw [hψ _ (div_pos (zero_lt_one.trans_le
    (one_le_norm (primaryPrimeFactor_spec hn hp).1.2.ne_zero)) hw)
      ((div_le_one hw).mpr (not_lt.mp h)),sub_self]

/-- The rough remainder also has uniformly bounded prime-factor count;
this is needed before replacing it by independent prime dyads. -/
theorem bounded_rough_primary_factors {ξ C : ℝ} (hξ : 0 < ξ) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψ : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ n : Eisenstein,
      primary n → Squarefree n → norm n ≤ C*X → roughProduct ψ (X^ξ) n ≠ 0 →
        (primaryPrimeFactors n).card < k := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ξ)
  have hk' : 1 < ξ*(k:ℝ) := by
    have hh := (div_lt_iff₀ hξ).mp hk
    nlinarith
  refine ⟨k,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_prime_tuple_norm_bound hC hk']
    with X hX hbound
  intro n hn hs hnX hne
  apply primary_factor_subset_card_lt hn hs (subset_refl _)
    (Real.one_le_rpow hX.le hξ.le) _ (hnX.trans_lt hbound)
  intro p hp
  exact (roughProduct_nonzero_prime_bound hψ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) hn hne hp).le

end CubicFirstMoment

end

end OAI
