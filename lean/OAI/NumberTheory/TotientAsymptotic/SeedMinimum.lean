import OAI.NumberTheory.TotientAsymptotic.SeedDivisibility
import OAI.NumberTheory.TotientAsymptotic.CofactorEnvelope

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace TotientAsymptotic

lemma seed_preimage_even {n : ℕ} (hn0 : 0<n) (hn : n.totient=2^18*257) : 2∣n := by
  by_contra h2
  have hfac : (3*5*17*257^2 : ℕ).factorization =
      Finsupp.single 3 1+Finsupp.single 5 1+Finsupp.single 17 1+Finsupp.single 257 2 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow,
      Nat.Prime.factorization (by norm_num : Nat.Prime 3),
      Nat.Prime.factorization (by norm_num : Nat.Prime 5),
      Nat.Prime.factorization (by norm_num : Nat.Prime 17),
      Nat.Prime.factorization (by norm_num : Nat.Prime 257)]
    simp
  have hd : n∣3*5*17*257^2 := by
    apply (Nat.factorization_prime_le_iff_dvd hn0.ne' (by norm_num)).mp
    intro p hp
    by_cases hpn : p∣n
    · have hm := Nat.mem_primeFactors.mpr ⟨hp,hpn,hn0.ne'⟩
      rcases seed_preimage_prime_choices hn hm with rfl|rfl|rfl|rfl|rfl|rfl
      · exact (h2 hpn).elim
      · have hb : n.factorization 3≤1 := by
          apply seed_factorization_bound hn0 hn hp
          rw [Nat.totient_prime_pow hp (by omega)]
          norm_num
        rw [hfac]
        convert hb using 1
        norm_num
      · have hb : n.factorization 5≤1 := by
          apply seed_factorization_bound hn0 hn hp
          rw [Nat.totient_prime_pow hp (by omega)]
          norm_num
        rw [hfac]
        convert hb using 1
        norm_num
      · have hb : n.factorization 17≤1 := by
          apply seed_factorization_bound hn0 hn hp
          rw [Nat.totient_prime_pow hp (by omega)]
          norm_num
        rw [hfac]
        convert hb using 1
        norm_num
      · have hb : n.factorization 257≤2 := by
          apply seed_factorization_bound hn0 hn hp
          rw [Nat.totient_prime_pow hp (by omega)]
          norm_num
        rw [hfac]
        convert hb using 1
        norm_num
      · exact (seed_not_large_fermat hn0 hn hpn).elim
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      exact Nat.zero_le _
  have hle := Nat.le_of_dvd (by norm_num : 0<3*5*17*257^2) hd
  have hφ := Nat.totient_le n
  rw [hn] at hφ
  omega

lemma seed_preimage_lower {n : ℕ} (hn0 : 0<n) (hn : n.totient=2^18*257) :
    135268352≤n := by
  have h257 : 257∣n := (dvd_pow_self 257 (by decide : 2≠0)).trans (seed_square_dvd hn0 hn)
  have htwo := seed_preimage_even hn0 hn
  have hsub : ({2,257} : Finset ℕ)⊆n.primeFactors := by
    intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,htwo,hn0.ne'⟩
    · exact Nat.mem_primeFactors.mpr ⟨by norm_num,h257,hn0.ne'⟩
  have he : (257/128 : ℝ) ≤ (n : ℝ)/n.totient := by
    rw [totient_ratio_product hn0]
    calc
      (257/128 : ℝ) = ∏ p∈({2,257} : Finset ℕ), (p : ℝ)/(p-1) := by norm_num
      _ ≤ _ := by
        apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
        · intro p hp
          have hpp := Nat.prime_of_mem_primeFactors (hsub hp)
          have hp1 : (1 : ℝ)<p := by exact_mod_cast hpp.one_lt
          exact div_nonneg (Nat.cast_nonneg _) (by linarith)
        · intro p hp _
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hp1 : (1 : ℝ)<p := by exact_mod_cast hpp.one_lt
          apply (le_div_iff₀ (by linarith)).mpr
          linarith
  rw [hn] at he
  have hnR : (135268352 : ℝ)≤n := by
    norm_num at he
    linarith
  exact_mod_cast hnR

/-- Exact published seed calculation, proved by finite prime-choice reduction
and Euler's product formula rather than an exhaustive search over integers. -/
theorem seed_least_preimage : ell (2^18*257)=135268352 := by
  apply Nat.le_antisymm
  · change ell (2^18*257)≤2^11*257^2
    apply ell_le (n := 2^11*257^2) (by positivity)
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (2^11) (257^2)),
      Nat.totient_prime_pow Nat.prime_two (by omega),
      Nat.totient_prime_pow (by norm_num : Nat.Prime 257) (by omega)]
    norm_num
  · exact seed_preimage_lower (ell_spec seed_isTotient).1 (ell_spec seed_isTotient).2

end TotientAsymptotic

end

end OAI
