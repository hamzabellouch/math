import OAI.NumberTheory.TotientAsymptotic.SeedArithmetic

namespace OAI

noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma seed_shift_coprime {n : ℕ} (hn : n.totient=2^18*257) :
    Nat.Coprime 257 (∏ p∈n.primeFactors, (p-1)) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  rcases seed_preimage_prime_choices hn hp with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

lemma seed_square_dvd {n : ℕ} (hn0 : 0<n) (hn : n.totient=2^18*257) :
    257^2 ∣ n := by
  have hC := seed_shift_coprime hn
  have he := Nat.totient_mul_prod_primeFactors n
  rw [hn] at he
  have hD : 257∣n := hC.dvd_mul_right.mp (he ▸
    (dvd_mul_of_dvd_left (by norm_num : 257∣2^18*257) _))
  have hp : 257∈n.primeFactors := (Nat.mem_primeFactors).mpr ⟨by norm_num,hD,hn0.ne'⟩
  have hprod : 257∣∏ p∈n.primeFactors,p := Finset.dvd_prod_of_mem _ hp
  have hD2 : 257^2∣(2^18*257)*(∏ p∈n.primeFactors,p) := by
    simpa only [pow_two] using mul_dvd_mul (by norm_num : 257∣2^18*257) hprod
  rw [he] at hD2
  exact (hC.pow_left 2).dvd_mul_right.mp hD2

lemma seed_not_large_fermat {n : ℕ} (hn0 : 0<n) (hn : n.totient=2^18*257) :
    ¬65537∣n := by
  intro hd
  have hboth : 257^2*65537∣n :=
    (show Nat.Coprime (257^2) 65537 by norm_num).mul_dvd_of_dvd_of_dvd (seed_square_dvd hn0 hn) hd
  have hφ := Nat.totient_dvd_of_dvd hboth
  rw [hn,Nat.totient_mul (by norm_num : Nat.Coprime (257^2) 65537),
    Nat.totient_prime_pow (by norm_num : Nat.Prime 257) (by omega),
    Nat.totient_prime (by norm_num : Nat.Prime 65537)] at hφ
  norm_num at hφ

lemma seed_factorization_bound {n p e : ℕ} (hn0 : 0<n) (hn : n.totient=2^18*257)
    (hp : p.Prime) (he : ¬(p^(e+1)).totient∣2^18*257) : n.factorization p≤e := by
  by_contra! h
  have hd := (hp.pow_dvd_iff_le_factorization hn0.ne').mpr h
  exact he (hn ▸ Nat.totient_dvd_of_dvd hd)

end TotientAsymptotic

end

end OAI
