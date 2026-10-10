import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPrimeIncidence

namespace OAI

/-! # Prime dilation on the literal quadratic coefficient array -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticPrimeTwist (p : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  v n * (jacobiSym (p : ℤ) n : ℂ)

theorem quadraticPrimeTwist_energy (p N : ℕ) (v : ℕ → ℂ) :
    quadraticSieveEnergy N (quadraticPrimeTwist p v) ≤ quadraticSieveEnergy N v := by
  apply Finset.sum_le_sum
  intro n _
  rcases jacobiSym.trichotomy (p : ℤ) n with h | h | h <;> simp [quadraticPrimeTwist, h]

theorem quadratic_prime_twist_identity {p : ℕ} (hp : p.Prime) (N : ℕ)
    (v : ℕ → ℂ) (m : ℤ) :
    quadraticTransposeSum N v m =
      quadraticTransposeSum N (quadraticPrimeTwist p v) ((p : ℤ) * m) +
        quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m := by
  unfold quadraticTransposeSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ := (Finset.mem_filter.mp hn).2.2.ne_zero
  unfold quadraticPrimeTwist
  rw [jacobiSym.mul_left, Int.cast_mul]
  by_cases hd : p ∣ n
  · have hc : ¬ p.Coprime n := by simpa only [hp.coprime_iff_not_dvd, not_not] using hd
    have hj : jacobiSym (p : ℤ) n = 0 := (jacobiSym.eq_zero_iff).mpr ⟨hn₀, by exact hc⟩
    simp [hd, hj]
  · have hc : p.Coprime n := hp.coprime_iff_not_dvd.mpr hd
    have hj : (jacobiSym (p : ℤ) n : ℂ) ^ 2 = 1 := by exact_mod_cast jacobiSym.sq_one (by exact hc)
    simp only [ite_eq_right hd, zero_mul, add_zero]
    calc
      _ = v n * (jacobiSym m n : ℂ) * (1 : ℂ) := by ring
      _ = v n * (jacobiSym m n : ℂ) * (jacobiSym (p : ℤ) n : ℂ) ^ 2 := by rw [hj]
      _ = _ := by ring

theorem quadratic_prime_twist_point_bound {p : ℕ} (hp : p.Prime) (N : ℕ)
    (v : ℕ → ℂ) (m : ℕ) :
    ‖quadraticTransposeSum N v m‖ ^ 2 ≤
      2 * ‖quadraticTransposeSum N (quadraticPrimeTwist p v) (p * m : ℕ)‖ ^ 2 +
        2 * ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖ ^ 2 := by
  rw [quadratic_prime_twist_identity hp N v m]
  have hh := norm_add_le
    (quadraticTransposeSum N (quadraticPrimeTwist p v) ((p : ℤ) * m))
    (quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  push_cast
  nlinarith [sq_nonneg (‖quadraticTransposeSum N (quadraticPrimeTwist p v) ((p : ℤ) * m)‖ -
    ‖quadraticTransposeSum N (fun n => if p ∣ n then v n else 0) m‖)]

end Ostmann

end OAI
