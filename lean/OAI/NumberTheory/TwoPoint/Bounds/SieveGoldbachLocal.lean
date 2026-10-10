import OAI.NumberTheory.EgyptianFractions.GoldbachSieveLocal
import OAI.NumberTheory.TwoPoint.Bounds.SieveEulerTruncation

namespace OAI

/-! The positive Euler factors of the actual binary Goldbach sieve. -/

namespace TwoPointCorrelations

open Finset Problem337
open scoped Classical

noncomputable def sieveGoldbachWeight (N p : ℕ) : ℝ :=
  goldbachSieveDensity N p / (1 - goldbachSieveDensity N p)

lemma sieve_goldbach_density_lt_one {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    goldbachSieveDensity N p < 1 :=
  goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN)

lemma sieve_goldbach_weight_pos {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    0 < sieveGoldbachWeight N p :=
  div_pos (goldbachSieveDensity_prime_pos N p hp)
    (sub_pos.mpr (sieve_goldbach_density_lt_one hN hp))

lemma sieve_goldbach_one_add {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    1 + sieveGoldbachWeight N p = (1 - goldbachSieveDensity N p)⁻¹ := by
  have h := ne_of_gt (sub_pos.mpr (sieve_goldbach_density_lt_one hN hp))
  unfold sieveGoldbachWeight
  field_simp
  ring

lemma sieve_goldbach_normalized {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    sieveGoldbachWeight N p / (1 + sieveGoldbachWeight N p) =
      goldbachSieveDensity N p := by
  have h := ne_of_gt (sub_pos.mpr (sieve_goldbach_density_lt_one hN hp))
  rw [sieve_goldbach_one_add hN hp]
  unfold sieveGoldbachWeight
  field_simp

lemma sieve_goldbach_mean_le {N : ℕ} (hN : 2 ∣ N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, sieveGoldbachWeight N p / (1 + sieveGoldbachWeight N p) * Real.log p) ≤
      2 * (∑ p ∈ P, Real.log (p : ℝ) / p) := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  rw [sieve_goldbach_normalized hN (hP p hp), goldbachSieveDensity_prime N p (hP p hp)]
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)
  split_ifs <;> simp only [div_eq_mul_inv] <;>
    nlinarith [mul_nonneg (inv_nonneg.mpr hpR.le) hlog]

lemma sieve_goldbach_factor_ge {N p : ℕ} (hN : 2 ∣ N) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ N then 1 - 1 / (p : ℝ) else 1) ≤
      1 + sieveGoldbachWeight N p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [sieve_goldbach_one_add hN hp, goldbachSieveDensity_prime N p hp]
  by_cases hdiv : p ∣ N
  · simp only [hdiv, ite_true]
    field_simp
    nlinarith
  · have hp2 : (2 : ℝ) < p := by
      have h : 2 < p := by
        have := hp.two_le
        by_contra hc
        have he : p = 2 := by omega
        exact hdiv (he ▸ hN)
      exact_mod_cast h
    have hp2ne : (p : ℝ) - 2 ≠ 0 := by linarith
    simp only [hdiv, ite_false, mul_one]
    have he : (1 - 1 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
      field_simp
    have hd : (1 - 2 / (p : ℝ))⁻¹ = (p : ℝ) / ((p : ℝ) - 2) := by
      field_simp
    rw [he, hd, div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith : (0 : ℝ) < p - 1))
      (by linarith : (0 : ℝ) < p - 2)).mpr
    nlinarith

end TwoPointCorrelations

end OAI
