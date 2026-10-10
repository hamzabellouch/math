import OAI.NumberTheory.TotientAsymptotic.TripleDiscriminant
import OAI.NumberTheory.TotientAsymptotic.SieveEulerProduct

namespace OAI

/-! The dimension-three lower bound for the collision sieve's Euler product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma tripleEulerProduct_eq (z : ℕ) (hz : 3 ≤ z) :
    primeEulerProduct z = 3*∏ p ∈ tripleSievePrimes z,(p:ℝ)/(p-1) := by
  classical
  have hthree : 3 ∈ oddSievePrimes z := by norm_num [mem_oddSievePrimes,hz]
  have hs : tripleSievePrimes z = (oddSievePrimes z).erase 3 := by
    ext p
    simp only [mem_tripleSievePrimes,mem_oddSievePrimes,Finset.mem_erase]
    constructor
    · rintro ⟨hpz,hpp,hp3⟩
      exact ⟨by omega,hpz,hpp,by omega⟩
    · rintro ⟨hp3,hpz,hpp,hp2⟩
      have hp := hpp.two_le
      exact ⟨hpz,hpp,by omega⟩
  rw [oddEulerProduct_eq z (by omega),hs,← Finset.mul_prod_erase _ _ hthree]
  norm_num
  ring

lemma tripleEulerProduct_log_lower (z : ℕ) (hz : 3 ≤ z) :
    Real.log z/3 ≤ ∏ p ∈ tripleSievePrimes z,(p:ℝ)/(p-1) := by
  have h := primeEulerProduct_log_lower z
  rw [tripleEulerProduct_eq z hz] at h
  linarith

lemma triple_exceptional_product_le_totient {D : ℕ} (hD : 0 < D) (z : ℕ) :
    (∏ p ∈ tripleSievePrimes z,if p ∣ D then ((p:ℝ)/(p-1))^2 else 1) ≤
      ((D:ℝ)/D.totient)^2 := by
  classical
  have hp : (∏ p ∈ (tripleSievePrimes z).filter (fun p => p ∣ D),(p:ℝ)/(p-1)) ≤
      (D:ℝ)/D.totient := by
    rw [totient_ratio_product hD]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      obtain ⟨hp,hd⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨(mem_tripleSievePrimes.mp hp).2.1,hd,hD.ne'⟩
    · intro p hp
      have hpp := (mem_tripleSievePrimes.mp (Finset.mem_filter.mp hp).1).2.1
      have hp1 : (1:ℝ) < p := by exact_mod_cast hpp.one_lt
      exact div_nonneg (Nat.cast_nonneg _) (by linarith)
    · intro p hp _
      have hp1 : (1:ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      apply (le_div_iff₀ (by linarith : (0:ℝ) < p-1)).mpr
      linarith
  rw [← Finset.prod_filter,Finset.prod_pow]
  apply pow_le_pow_left₀ _ hp 2
  apply Finset.prod_nonneg
  intro p hp
  have hp1 : (1:ℝ) < p := by
    exact_mod_cast (mem_tripleSievePrimes.mp (Finset.mem_filter.mp hp).1).2.1.one_lt
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

lemma tripleSieveEulerProduct_lower {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (z : ℕ) (hz : 3 ≤ z) :
    (Real.log z)^3/27 ≤ (∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p))*
      ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2 := by
  have hfactor : (∏ p ∈ tripleSievePrimes z,(p:ℝ)/(p-1))^3 ≤
      (∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p))*
        (∏ p ∈ tripleSievePrimes z,if p ∣ tripleDiscriminant a b then ((p:ℝ)/(p-1))^2 else 1) := by
    rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro p hp
      have hpR : (3:ℝ) < p := by exact_mod_cast (mem_tripleSievePrimes.mp hp).2.2
      exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (by linarith)) 3
    · intro p hp
      exact tripleSieveWeight_euler_factor hab (mem_tripleSievePrimes.mp hp).2.1
        (mem_tripleSievePrimes.mp hp).2.2
  have hp : 0 ≤ ∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p) :=
    Finset.prod_nonneg (fun p hp => by have := tripleSieveWeight_nonneg a b hp; linarith)
  have he := mul_le_mul_of_nonneg_left
    (triple_exceptional_product_le_totient (tripleDiscriminant_pos ha hab) z) hp
  have hl := pow_le_pow_left₀ (show 0 ≤ Real.log z/3 by
    have hz1 : (1:ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
    exact div_nonneg (Real.log_nonneg hz1) (by norm_num))
    (tripleEulerProduct_log_lower z hz) 3
  calc
    _ = (Real.log z/3)^3 := by ring
    _ ≤ _ := hl
    _ ≤ _ := hfactor.trans he

end TotientAsymptotic

end

end OAI
