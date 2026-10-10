import OAI.NumberTheory.Ostmann.QuadraticCenter.OuterFrequencyCutoff
import OAI.NumberTheory.Ostmann.Construction.PrimeProductTranslations

namespace OAI

/-! # The genuine outer divisors fit the fixed arithmetic family -/

namespace Ostmann

open scoped BigOperators

theorem primeProduct_divisors_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k M : ℕ) (hM : M ∈ primeSubsetProducts P k) : M.divisors.card = 2 ^ k := by
  obtain ⟨U, hU, hprod⟩ := Finset.mem_image.mp hM
  obtain ⟨hUP, hcard⟩ := Finset.mem_powersetCard.mp hU
  have hh := sum_primeSet_divisors U (fun p hp => hP p (hUP hp)) (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, mul_one] at hh
  have hn : U.toList.prod.divisors.card = 2 ^ U.card := by exact_mod_cast hh
  have hp : U.toList.prod = M := by simpa only [Finset.prod_toList] using hprod
  simpa only [hp, hcard] using hn

theorem primeProduct_divisor_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k M d : ℕ) (A : ℝ) (hmin : ∀ p ∈ P, A ≤ (p : ℝ))
    (hM : M ∈ primeSubsetProducts P k) (hd : d ∈ M.divisors.erase 1) : A ≤ d := by
  obtain ⟨hd1, hdM⟩ := Finset.mem_erase.mp hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hM0 := (Nat.mem_divisors.mp hdM).2
  have hpM : p ∈ M.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, hpd.trans (Nat.mem_divisors.mp hdM).1, hM0⟩
  obtain ⟨U, hU, hprod⟩ := Finset.mem_image.mp hM
  have hUP := (Finset.mem_powersetCard.mp hU).1
  have hf : M.primeFactors = U := by
    rw [← hprod, Nat.primeFactors_prod (fun q hq => hP q (hUP hq))]
  have hpP := hUP (hf ▸ hpM)
  exact (hmin p hpP).trans (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_mem_divisors hdM) hpd))

theorem outerDivisor_upper (T : ℝ) (N d : ℕ)
    (hN : (N : ℝ) ≤ Real.exp (14 * T)) (hd : d ^ 2 ≤ N) :
    (d : ℝ) ≤ Real.exp (7 * T) := by
  have hh : (d : ℝ) ^ 2 ≤ Real.exp (14 * T) := (by exact_mod_cast hd : (d : ℝ) ^ 2 ≤ N).trans hN
  have he : Real.exp (7 * T) ^ 2 = Real.exp (14 * T) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  nlinarith [Real.exp_pos (7 * T), Nat.cast_nonneg (α := ℝ) d]

end Ostmann

end OAI
