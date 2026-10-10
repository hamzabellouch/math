import OAI.NumberTheory.JointDickman.Amplification.TiltedPrefixMeans

namespace OAI

/-! # The numeric-addition sieve product after coefficient primes are deleted -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem prefix_reciprocal_removed_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ g ε : ℝ}
    (hκ : 0 < κ) (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ E : Finset ℕ, E ⊆ auxiliaryPrimes B →
      (∏ p ∈ E, p : ℕ) ≤ Real.exp (κ*B) →
      (g-ε)*auxiliaryLogLength B ≤
        ∑ p ∈ primePrefix B g (auxiliaryPrimes B) \ E, 1/(p : ℝ) := by
  have hm := prefix_reciprocal_mean_tendsto hM hg hg1
  filter_upwards [hm.eventually (Ioi_mem_nhds (by linarith : g-ε/2 < g)),
    auxiliary_selected_reciprocal_sum_small hκ,
    auxiliaryLogLength_tendsto.eventually_ge_atTop (2/ε),
    auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hmean hEbound hlarge hℓ
  intro E hE hprod
  let Q := primePrefix B g (auxiliaryPrimes B)
  have hsum : (g-ε/2)*auxiliaryLogLength B ≤ ∑ p ∈ Q, 1/(p : ℝ) :=
    ((lt_div_iff₀ hℓ).mp hmean).le
  have herr : (∑ p ∈ Q ∩ E, 1/(p : ℝ)) ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg inter_subset_right (by intros; positivity)).trans (hEbound E hE hprod)
  have he := sum_sdiff (f := fun p : ℕ => 1/(p : ℝ)) (show Q ∩ E ⊆ Q from inter_subset_left)
  have hset : Q \ (Q ∩ E) = Q \ E := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hset] at he
  have hlarge' := (div_le_iff₀ hε).mp hlarge
  nlinarith

theorem numeric_sieve_prefix_product
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ g ε : ℝ}
    (hκ : 0 < κ) (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ (E : Finset ℕ) (q : ℝ), E ⊆ auxiliaryPrimes B →
      (∏ p ∈ E, p : ℕ) ≤ Real.exp (κ*B) → 0 ≤ q → q ≤ 1 →
      (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ E, (1-(3/2-q)/(p : ℝ))) ≤
        Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B) := by
  filter_upwards [prefix_reciprocal_removed_lower hM hκ hg hg1 (half_pos hε),
    auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hsum hℓ
  intro E q hE hprod hq hq1
  let P := primePrefix B g (auxiliaryPrimes B) \ E
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    apply auxiliaryPrimes_prime B p
    have hQ : primePrefix B g (auxiliaryPrimes B) ⊆ auxiliaryPrimes B := by
      unfold primePrefix
      split_ifs
      · exact filter_subset _ _
      · exact subset_rfl
    exact hQ (mem_sdiff.mp hp).1
  have hprodexp : (∏ p ∈ P, (1-(3/2-q)/(p : ℝ))) ≤
      Real.exp (-(3/2-q)*(∑ p ∈ P, 1/(p : ℝ))) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (-(3/2-q)/(p : ℝ)) := by
        apply prod_le_prod₀
        · intro p hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
          apply sub_nonneg.mpr
          exact (div_le_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)
        · intro p _
          simpa only [neg_div,sub_eq_add_neg,add_comm] using
            Real.add_one_le_exp (-(3/2-q)/(p : ℝ))
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro p _
        ring
  refine hprodexp.trans (Real.exp_le_exp.mpr ?_)
  have hm := hsum E hE hprod
  have hc : 0 ≤ 3/2-q := by linarith
  have hh := mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr hc)
  have hεℓ := mul_nonneg hε.le hℓ.le
  nlinarith

end JointDickman

end OAI
