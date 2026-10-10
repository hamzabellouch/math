import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleDecomposition

namespace OAI

/-! Uniformly bounded tuple lengths in the manuscript's actual
prime detector. The bound depends on xi, not on the envelope scale. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventually_prime_tuple_norm_bound {ξ C : ℝ} (hC : 0 < C)
    {k : ℕ} (hk : 1 < ξ*(k:ℝ)) :
    ∀ᶠ X : ℝ in atTop, C*X < (X^ξ)^k := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_rpow_le hk (2*C)] with X hX h
  rw [Real.rpow_one] at h
  rw [←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hX).le]
  nlinarith [mul_pos hC (zero_lt_one.trans hX)]

lemma distinguished_subset_card_lt {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 1 ≤ w) (hwz : w ≤ z)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n)
    (hne : (∏ p ∈ s, distinguishedPrimeWeight ψ w z p) ≠ 0)
    {k : ℕ} (hsize : norm n < w^k) : s.card < k := by
  apply primary_factor_subset_card_lt hn hs hsub hw _ hsize
  intro p hp
  exact (distinguishedPrimeWeight_support hψone hψzero (zero_lt_one.trans_le hw) hwz
    (zero_lt_one.trans_le (one_le_norm (primaryPrimeFactor_spec hn (hsub hp)).1.2.ne_zero))
    ((Finset.prod_ne_zero_iff.mp hne) p hp)).1.le

/-- The actual ordered distinguished expansion can be cut off at one
fixed tuple length throughout a whole norm envelope. -/
theorem bounded_distinguished_primary_tuples {ξ C : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C)
    {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∃ k : ℕ, ∀ᶠ X : ℝ in atTop, ∀ n : Eisenstein,
      primary n → Squarefree n → norm n ≤ C*X →
      (roughProduct ψ (X^(2/5:ℝ)) n:ℂ) =
        ∑ s ∈ (primaryPrimeFactors n).powerset with s.card < k,
          ((s.card.factorial:ℂ)⁻¹)*
            (∑ e : Fin s.card ≃ s,
              ∏ i : Fin s.card, distinguishedPrimeWeight ψ (X^ξ) (X^(2/5:ℝ)) (e i))*
            (roughProduct ψ (X^ξ) (primaryFactorRemainder n s):ℂ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ξ)
  have hk' : 1 < ξ*(k:ℝ) := by
    have hh := (div_lt_iff₀ hξ).mp hk
    nlinarith
  refine ⟨k,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_prime_tuple_norm_bound hC hk']
    with X hX hbound
  intro n hn hs hnX
  rw [roughProduct_ordered_primary_tuples hn]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s hsP hsfilter
  have hsub := Finset.mem_powerset.mp hsP
  have hcard : ¬s.card < k := by simpa only [Finset.mem_filter,hsP,true_and] using hsfilter
  have hpzero : (∏ p ∈ s, distinguishedPrimeWeight ψ (X^ξ) (X^(2/5:ℝ)) p) = 0 := by
    by_contra hne
    exact hcard (distinguished_subset_card_lt hn hs hψone hψzero
      (Real.one_le_rpow hX.le hξ.le) (Real.rpow_le_rpow_of_exponent_le hX.le hξz)
      hsub hne (hnX.trans_lt hbound))
  rw [ordered_subset_product,hpzero,zero_mul]

end CubicFirstMoment

end

end OAI
