import OAI.NumberTheory.Ostmann.QuadraticSieve.JacobiFamilyMoment
import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetProducts
import OAI.NumberTheory.Ostmann.Preliminaries.FallingFactorialError

namespace OAI

/-! # Transferring the finite-family moment to products of distinct primes -/

namespace Ostmann

open scoped BigOperators

theorem inverse_choose_le (J k : ℕ) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ J) :
    ((J.choose k : ℝ))⁻¹ ≤ 2 * (k.factorial : ℝ) / (J : ℝ) ^ k := by
  have hJ : 0 < J := by nlinarith
  have hkJ : k ≤ J := by nlinarith
  have hp : J ^ k = J * J ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
  have hb := pow_le_descFactorial_add J hJ k
  have hloss := Nat.mul_le_mul_right (J ^ (k - 1)) hsize
  have hbound : J ^ k ≤ 2 * J.descFactorial k := by nlinarith
  have hchoose : (0 : ℝ) < J.choose k := by exact_mod_cast Nat.choose_pos hkJ
  have hJpow : (0 : ℝ) < (J : ℝ) ^ k := by positivity
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hchoose hJpow).mpr
  have hh : (J : ℝ) ^ k ≤ 2 * ((k.factorial : ℝ) * (J.choose k : ℝ)) := by
    exact_mod_cast (show J ^ k ≤ 2 * (k.factorial * J.choose k) by
      rwa [Nat.descFactorial_eq_factorial_mul_choose] at hbound)
  nlinarith

/-- Positivity transfers any statistic of the prime product to all odd
moduli in its range; unique factorization gives the exact uniform weight. -/
theorem prime_product_mean_le_odd_sum (P : Finset ℕ) (k Z : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (hZ : ∀ p ∈ P, p ≤ Z) (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    (P.card.choose k : ℝ)⁻¹ * (∑ m ∈ primeSubsetProducts P k, F m) ≤
      (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ Finset.range (Z ^ k + 1), if Odd m then F m else 0) := by
  classical
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hmem := primeSubsetProducts_mem_range P k Z hP hodd hZ
  have hs : primeSubsetProducts P k ⊆ Finset.range (Z ^ k + 1) := by
    intro m hm
    have hh := (Finset.mem_filter.mp (hmem hm)).1
    have hh' := (Finset.mem_Icc.mp hh).2
    exact Finset.mem_range.mpr (by omega)
  have heq : (∑ m ∈ primeSubsetProducts P k, F m) =
      ∑ m ∈ primeSubsetProducts P k, if Odd m then F m else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    have ho := (Finset.mem_filter.mp (hmem hm)).2.1
    simp only [ho, ite_true]
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg hs
  intro m hm hnot
  split <;> simp_all

/-- This is the finite, explicit version of the manuscript's uniform
Jacobi-family moment estimate, before its final numerical specialization. -/
theorem prime_product_family_moment_bound (hB : PublishedBonamiBound)
    {I : Type*} [Fintype I] (P S R : Finset ℕ)
    (hS : ∀ s ∈ S, Squarefree s) (hR : ∀ s ∈ S, s.primeFactors ⊆ R)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, Odd p)
    (U Z k l : ℕ) (hU : ∀ s ∈ S, s ≤ U) (hZ : ∀ p ∈ P, p ≤ Z)
    (hl : 0 < l) (hk : 1 ≤ k) (hsize : 2 * k ^ 2 ≤ P.card)
    (b : I → S → ℂ) (pick : ℕ → I) (E A : ℝ)
    (henergy : ∀ i, (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b i s‖ ^ 2) ≤ E)
    (hmass : ∀ i, (∑ s : S, ‖b i s‖) ≤ A) :
    (P.card.choose k : ℝ)⁻¹ *
        (∑ m ∈ primeSubsetProducts P k,
          ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l)) ≤
      (2 * (k.factorial : ℝ) / (P.card : ℝ) ^ k) *
        ((Fintype.card I : ℝ) * (2 : ℝ) ^ (2 * l) *
          (((Z ^ k + 1 : ℕ) : ℝ) * E ^ l +
            (8 * (U : ℝ) ^ (2 * l)) * A ^ (2 * l))) := by
  classical
  have hdom := prime_product_mean_le_odd_sum P k Z hP hodd hZ
    (fun m => ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l))
    (fun _ => by positivity)
  have hm := complex_odd_jacobi_chosen_moment_bound hB R S hS hR U (Z ^ k + 1) l
    hU hl b pick E A henergy hmass
  have hoddnonneg : 0 ≤ ∑ m ∈ Finset.range (Z ^ k + 1),
      if Odd m then ‖∑ s : S, b (pick m) s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0 := by
    apply Finset.sum_nonneg
    intro m hm
    split <;> positivity
  exact hdom.trans ((mul_le_mul_of_nonneg_right (inverse_choose_le P.card k hk hsize)
    hoddnonneg).trans (mul_le_mul_of_nonneg_left hm (by positivity)))

end Ostmann

end OAI
