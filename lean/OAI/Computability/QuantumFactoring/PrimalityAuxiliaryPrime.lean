import Mathlib

namespace OAI

section


namespace ExactQuantumFactoring.Primality
open scoped BigOperators

/-- A quantitative bound at the manuscript's unchanged cutoff n^8. We reuse
Mathlib's proved Chebyshev bound instead of repeating its binomial argument. -/
lemma primorial_gt_cutoff {n : ℕ} (hn : 128 ≤ n) :
    2^(n^6) < primorial (n^8) := by
  have hnR : (128 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hl2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2' : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hlog : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
  have hlog8 : Real.log ((n : ℝ)^8+1) ≤ 1+8*(n : ℝ) := by
    have h8 : (1 : ℝ) ≤ (n : ℝ)^8 := one_le_pow₀ hn1
    calc
      Real.log ((n : ℝ)^8+1) ≤ Real.log (2*(n : ℝ)^8) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + 8*Real.log (n : ℝ) := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
      _ ≤ 1+8*(n : ℝ) := by linarith
  have hsqrt : Real.sqrt ((n : ℝ)^8) = (n : ℝ)^4 := by
    rw [show (n : ℝ)^8 = ((n : ℝ)^4)^2 by ring, Real.sqrt_sq (by positivity)]
  have ht := Chebyshev.theta_ge (n^8)
  simp only [Nat.cast_pow, hsqrt, Real.log_pow, Nat.cast_ofNat] at ht
  have h6pos : (0 : ℝ) < (n : ℝ)^6 := by positivity
  have h6one : (1 : ℝ) ≤ (n : ℝ)^6 := one_le_pow₀ hn1
  have hn6 : (n : ℝ) ≤ (n : ℝ)^6 := le_self_pow₀ hn1 (by decide : 6 ≠ 0)
  have h56 : (n : ℝ)^5 ≤ (n : ℝ)^6 := pow_le_pow_right₀ hn1 (by decide)
  have h86 : (128 : ℝ)^2*(n : ℝ)^6 ≤ (n : ℝ)^8 := by
    calc
      (128 : ℝ)^2*(n : ℝ)^6 ≤ (n : ℝ)^2*(n : ℝ)^6 := by gcongr
      _ = (n : ℝ)^8 := by ring
  have hmain : (n : ℝ)^6 < Chebyshev.theta (n^8) := by
    have hmul := mul_le_mul_of_nonneg_left hl2 (show (0 : ℝ) ≤ (n : ℝ)^8 by positivity)
    have hlogmul := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 16*(n : ℝ)^4 by positivity)
    have hlogmul' : 16*(n : ℝ)^4*Real.log (n : ℝ) ≤ 16*(n : ℝ)^5 := by
      calc
        _ ≤ 16*(n : ℝ)^4*(n : ℝ) := hlogmul
        _ = _ := by ring
    nlinarith only [ht, hmul, hlogmul', hlog8, h86, h6one, hn6, h56]
  have hlogpow : Real.log ((2^(n^6) : ℕ) : ℝ) <
      Real.log (primorial (n^8) : ℝ) := by
    rw [Chebyshev.theta_eq_log_primorial] at hmain
    simp only [← Nat.cast_pow, Nat.floor_natCast] at hmain
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    exact (mul_lt_mul_of_pos_left hl2' h6pos).trans_le (by simpa only [Nat.cast_pow, mul_one] using hmain.le)
  have := (Real.log_lt_log_iff (by positivity) (by exact_mod_cast primorial_pos (n^8))).mp hlogpow
  exact_mod_cast this

/-- The finite integer excluded by the auxiliary-prime search. -/
def badProduct (n m : ℕ) : ℕ := m * ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1)

lemma badProduct_pos {n m : ℕ} (hm : 2 ≤ m) : 0 < badProduct n m := by
  apply Nat.mul_pos (by omega)
  apply Finset.prod_pos
  intro j hj
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjm : 2 ≤ m^j := by
    exact hm.trans (Nat.le_pow (by omega))
  omega

lemma badProduct_lt_cutoff {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n) :
    badProduct n m < 2^(n^6) := by
  have hp : ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1) ≤ m^(n^4) := by
    calc
      ∏ j ∈ Finset.Icc 1 (n^2), (m^j-1) ≤ ∏ _j ∈ Finset.Icc 1 (n^2), m^(n^2) := by
        apply Finset.prod_le_prod
        intro j hj
        exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by omega) (Finset.mem_Icc.mp hj).2)
      _ = m^(n^4) := by simp [← pow_mul]; congr 1; ring
  have hexp : n*(1+n^4) < n^6 := by
    have hn1 : 1 ≤ n := by omega
    have hn4 : 1 ≤ n^4 := Nat.one_le_pow _ _ hn1
    have hn2 : 2*n ≤ n^2 := by nlinarith
    have h56 : n^5 < n^6 := Nat.pow_lt_pow_right (by omega) (by decide)
    have h46 : 2*n^5 ≤ n^6 := by
      calc
        2*n^5 = (2*n)*n^4 := by ring
        _ ≤ n^2*n^4 := Nat.mul_le_mul_right _ hn2
        _ = n^6 := by ring
    have hn5 : n < n^5 := by simpa using Nat.pow_lt_pow_right (by omega : 1 < n) (by decide : 1 < 5)
    nlinarith
  calc
    badProduct n m ≤ m^(1+n^4) := by simpa [badProduct, pow_add] using Nat.mul_le_mul_left m hp
    _ < (2^n)^(1+n^4) := Nat.pow_lt_pow_left hmb (by omega)
    _ = 2^(n*(1+n^4)) := (pow_mul _ _ _).symm
    _ < 2^(n^6) := Nat.pow_lt_pow_right (by decide) hexp

/-- The auxiliary prime searched for by the source algorithm exists within n^8;
no number-theoretic existence oracle is included in the algorithm. -/
theorem auxiliary_prime_exists {n m : ℕ} (hn : 128 ≤ n) (hm : 2 ≤ m) (hmb : m < 2^n) :
    ∃ s : ℕ, s.Prime ∧ s ≤ n^8 ∧ s.Coprime m ∧ n^2 < orderOf (m : ZMod s) := by
  have hpgt := primorial_gt_cutoff hn
  have hb := badProduct_lt_cutoff hn hm hmb
  have hex : ∃ s ∈ Nat.primesLE (n^8), ¬ s ∣ badProduct n m := by
    by_contra h
    have hall : ∀ s ∈ Nat.primesLE (n^8), s ∣ badProduct n m := by simpa using h
    have hd : primorial (n^8) ∣ badProduct n m := by
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_primes_dvd _ (fun s hs => (Nat.mem_primesLE.mp hs).2.prime) hall
    exact (not_lt_of_ge (Nat.le_of_dvd (badProduct_pos hm) hd)) (hb.trans hpgt)
  obtain ⟨s,hs,hbad⟩ := hex
  have hs' := (Nat.mem_primesLE.mp hs).2
  have hsm : ¬ s ∣ m := fun hd => hbad (dvd_mul_of_dvd_left hd _)
  have hcop := hs'.coprime_iff_not_dvd.mpr hsm
  refine ⟨s,hs',(Nat.mem_primesLE.mp hs).1,hcop,?_⟩
  let : Fact s.Prime := ⟨hs'⟩
  have hopos : 0 < orderOf (m : ZMod s) :=
    ((ZMod.isUnit_iff_coprime m s).mpr hcop.symm).isOfFinOrder.orderOf_pos
  by_contra h
  have ho : orderOf (m : ZMod s) ∈ Finset.Icc 1 (n^2) := Finset.mem_Icc.mpr ⟨hopos,by omega⟩
  have hpow : s ∣ m^(orderOf (m : ZMod s))-1 := by
    rw [← ZMod.natCast_eq_zero_iff (b := s)]
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_one, Nat.cast_pow,
      pow_orderOf_eq_one, sub_self]
  exact hbad (dvd_mul_of_dvd_right (hpow.trans (Finset.dvd_prod_of_mem (fun j => m^j-1) ho)) m)

end ExactQuantumFactoring.Primality


end

end OAI
