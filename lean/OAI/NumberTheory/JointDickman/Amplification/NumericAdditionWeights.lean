import OAI.NumberTheory.JointDickman.Arithmetic.AdditionProgressionSieve
import OAI.NumberTheory.JointDickman.Probability.ArithmeticSplitWeights

namespace OAI

/-! # Dropping prime conditions in the numeric-addition sieve -/

namespace JointDickman
open Finset Classical

theorem prime_product_weight_le_residue_product (S P : Finset ℕ) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hS : ∀ p ∈ S, p.Prime) (hP : ∀ p ∈ P, p.Prime) :
    q^S.card ≤ ∏ p ∈ P, residueWeight q 0 ((∏ r ∈ S, r : ℕ) : ZMod p) := by
  let n := ∏ r ∈ S, r
  have hn : n ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  have hpf : n.primeFactors = S := Nat.primeFactors_prod hS
  have hdiv (p : ℕ) (hp : p ∈ P) : p ∣ n ↔ p ∈ S := by
    rw [← hpf,Nat.mem_primeFactors]
    simp only [hP p hp,hn,and_true,true_and,ne_eq,not_false_eq_true]
  have he (p : ℕ) (hp : p ∈ P) : residueWeight q 0 (n : ZMod p) = if p ∈ S then q else 1 := by
    simp only [residueWeight,ZMod.natCast_eq_zero_iff,hdiv p hp]
  have hs : P.filter (fun p => p ∈ S) ⊆ S := fun p hp => (mem_filter.mp hp).2
  have hh := prod_le_prod_of_subset_of_le_one₀ hs (f := fun _ : ℕ => q)
    (fun _ _ => hq) (fun _ _ _ => hq1)
  change q^S.card ≤ ∏ p ∈ P, residueWeight q 0 (n : ZMod p)
  rw [prod_congr rfl he,← prod_filter]
  simpa only [prod_const] using hh

theorem prefix_count_weight_le_residue_product (n : ℕ) (Q P : Finset ℕ)
    (hn : n ≠ 0) (hPQ : P ⊆ Q) (hP : ∀ p ∈ P, p.Prime) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    q^(n.primeFactors ∩ Q).card ≤ ∏ p ∈ P, residueWeight q 0 (n : ZMod p) := by
  let S := n.primeFactors ∩ Q
  have he (p : ℕ) (hp : p ∈ P) : residueWeight q 0 (n : ZMod p) = if p ∈ S then q else 1 := by
    have hd : p ∈ S ↔ p ∣ n := by
      simp only [S,mem_inter,Nat.mem_primeFactors,hP p hp,hn,hPQ hp,and_true,true_and,ne_eq,not_false_eq_true]
    simp only [residueWeight,ZMod.natCast_eq_zero_iff,hd]
  have hs : P.filter (fun p => p ∈ S) ⊆ S := fun p hp => (mem_filter.mp hp).2
  have hh := prod_le_prod_of_subset_of_le_one₀ hs (f := fun _ : ℕ => q)
    (fun _ _ => hq) (fun _ _ _ => hq1)
  rw [prod_congr rfl he,← prod_filter]
  simpa only [prod_const,S] using hh

/-- Prefix regularity of the alternative quotient supplies its half-weight.
Deleting all other prime conditions increases the numeric sum. -/
theorem regular_numeric_addition_majorant {B L k n : ℕ} {τ C q : ℝ}
    (S P : Finset ℕ) (hn : n ≠ 0) (hk : k ∈ Icc 1 L)
    (hreg : RegularPrimeSet B L τ C (coefficientPrimeSet B n))
    (hP : P ⊆ primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B))
    (hS : ∀ p ∈ S, p.Prime) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    q^S.card ≤ Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
      ∏ p ∈ P, residueWeight q 0 ((∏ r ∈ S, r : ℕ) : ZMod p)*residueWeight (1/2) 0 (n : ZMod p) := by
  let Q := primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B)
  have hPprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    apply auxiliaryPrimes_prime B p
    have hsub : Q ⊆ auxiliaryPrimes B := by
      unfold Q primePrefix
      split_ifs
      · exact filter_subset _ _
      · exact subset_rfl
    exact hsub (hP hp)
  have hz := prime_product_weight_le_residue_product S P hq hq1 hS hPprime
  have hc := prefix_count_weight_le_residue_product n Q P hn hP hPprime (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have hncard : ((n.primeFactors ∩ Q).card : ℝ) ≤ (((k : ℝ)/L)/2+τ)*auxiliaryLogLength B := by
    have hh := (hreg.1 k hk).2
    rwa [coefficient_prefix_count hn] at hh
  have hweight : 1 ≤ Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
      (1/2 : ℝ)^(n.primeFactors ∩ Q).card := by
    have hp : (1/2 : ℝ)^(n.primeFactors ∩ Q).card =
        Real.exp (-((n.primeFactors ∩ Q).card : ℝ)*Real.log 2) := by
      rw [show -((n.primeFactors ∩ Q).card : ℝ)*Real.log 2 =
        ((n.primeFactors ∩ Q).card : ℝ)*(-Real.log 2) by ring,
        Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hp,← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
  calc
    _ ≤ q^S.card*(Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
        (1/2 : ℝ)^(n.primeFactors ∩ Q).card) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hweight (pow_nonneg hq _)
    _ = Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
        (q^S.card*(1/2 : ℝ)^(n.primeFactors ∩ Q).card) := by ring
    _ ≤ Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
        ((∏ p ∈ P, residueWeight q 0 ((∏ r ∈ S, r : ℕ) : ZMod p))*
          (∏ p ∈ P, residueWeight (1/2) 0 (n : ZMod p))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul hz hc (by positivity) (prod_nonneg (fun _ _ => residueWeight_nonneg _ _ hq))
    _ = _ := by rw [prod_mul_distrib]

end JointDickman

end OAI
