import OAI.NumberTheory.JointDickman.Amplification.RequiredSubsetTail
import OAI.NumberTheory.JointDickman.Amplification.WeightedRemainderLaw
import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryOdds
import OAI.NumberTheory.JointDickman.Amplification.PrefixOmissions

namespace OAI

/-! # Availability of a fixed addition under the tilted remainder law -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem tilted_required_product (Z : Finset ℕ) (hZ : ∀ p ∈ Z, p.Prime) :
    (∏ p ∈ Z, 1/(2*(p : ℝ)-1)) =
      ((1/2 : ℝ)^Z.card/(∏ p ∈ Z, p : ℕ))*
        ∏ p ∈ Z, (1-(1/2 : ℝ)/p)⁻¹ := by
  have he (p : ℕ) (hp : p ∈ Z) :
      1/(2*(p : ℝ)-1) = ((1/2 : ℝ)/(p : ℝ))*(1-(1/2 : ℝ)/p)⁻¹ := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hZ p hp).ne_zero
    field_simp [hp0]
  rw [prod_congr rfl he,prod_mul_distrib,prod_div_distrib,prod_const,Nat.cast_prod]

/-- The odds correction is uniformly bounded for every allowed numeric
addition; its squarefree product is in the actual coefficient range. -/
theorem tilted_required_product_bound :
    ∀ᶠ B : ℕ in atTop, ∀ Z : Finset ℕ, Z ⊆ auxiliaryPrimes B →
      (∏ p ∈ Z, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
      (∏ p ∈ Z, 1/(2*(p : ℝ)-1)) ≤
        Real.exp 1*((1/2 : ℝ)^Z.card/(∏ p ∈ Z, p : ℕ)) := by
  filter_upwards [auxiliary_selected_odds_bound] with B hB
  intro Z hZ hsize
  rw [tilted_required_product Z (fun p hp => auxiliaryPrimes_prime B p (hZ hp))]
  have hnon : 0 ≤ (1/2 : ℝ)^Z.card/(∏ p ∈ Z, p : ℕ) := by positivity
  exact (mul_le_mul_of_nonneg_left (hB Z hZ hsize) hnon).trans_eq (mul_comm _ _)

/-- Regularity is retained inside the probability. No conditional
probability or reciprocal of a regularity event occurs. -/
theorem tilted_addition_regular_tail {B L k : ℕ} {τ C : ℝ}
    (A Z : Finset ℕ) (hZ : Z ⊆ auxiliaryPrimes B \ A)
    (hk : k ∈ Icc 1 L)
    (hprefix : Z ⊆ primePrefix B ((k : ℝ)/L) Z)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ R ∈ (auxiliaryPrimes B \ A).powerset,
      if Z ⊆ R ∧ RegularPrimeSet B L τ C R then
        bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) R else 0) ≤
      (∏ p ∈ Z, 1/(2*(p : ℝ)-1))*
        Real.exp (t*((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B-Z.card)+
          (Real.exp (-t)-1)*
            ∑ p ∈ ((auxiliaryPrimes B \ A) \ Z) ∩
              primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B), 1/(2*(p : ℝ)-1)) := by
  let P := auxiliaryPrimes B \ A
  let Q := primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B)
  let q := fun p : ℕ => 1/(2*(p : ℝ)-1)
  have hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
    exact ⟨div_nonneg (by norm_num) (by linarith),(div_le_one (by linarith)).mpr (by linarith)⟩
  have hZQ : Z ⊆ Q := hprefix.trans (primePrefix_mono B _ (hZ.trans sdiff_subset))
  refine le_trans ?_ (bernoulliSubsetMass_required_prefix_tail P Z Q q hZ hZQ hq ht
    ((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B))
  apply sum_le_sum
  intro R hR
  have hr := mem_powerset.mp hR
  have hnon := bernoulliSubsetMass_nonneg hr hq
  split_ifs with hgood hcount
  · exact le_rfl
  · exfalso
    apply hcount
    refine ⟨hgood.1,?_⟩
    have he : R ∩ Q = primePrefix B ((k : ℝ)/L) R := by
      dsimp [Q]
      rw [← primePrefix_inter,inter_eq_left.mpr (hr.trans sdiff_subset)]
    rw [he]
    exact (hgood.2.1 k hk).2
  · exact hnon
  · exact le_rfl

end JointDickman

end OAI
