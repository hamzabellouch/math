import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowth
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainder
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareRemoval

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem truncatedMainAlpha_factors {K Δ w : ℕ} (ha : truncatedMainAlpha K Δ w ≠ 0) :
    ∃ r s : ℕ, Squarefree r ∧ s ∣ Δ ∧ w = s ^ 2 * r := by
  unfold truncatedMainAlpha at ha
  split_ifs at ha with ho
  · obtain ⟨e, he, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
    have hc : e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K := by
      by_contra hn
      simp [hn] at hne
    rw [ite_eq_left hc] at hne
    have hes : Squarefree e := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hne
    refine ⟨gcdReducedModulus e (w / e), e.gcd (w / e),
      gcdReducedModulus_squarefree hes hc.2.1,
      (Nat.gcd_dvd_left e (w / e)).trans (Nat.mem_divisors.mp he).1, ?_⟩
    rw [← mul_eq_gcd_sq_mul_reduced, Nat.mul_div_cancel' hc.1]
  · exact (ha rfl).elim

theorem truncatedMainBeta_factors {K Δ w : ℕ} (hb : truncatedMainBeta K Δ w ≠ 0) :
    ∃ r s : ℕ, Squarefree r ∧ s ∣ Δ ∧ w = s ^ 2 * r := by
  unfold truncatedMainBeta at hb
  split_ifs at hb with ho
  · obtain ⟨s, hs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    have hc : s ^ 2 ∣ w ∧ Squarefree (w / s ^ 2) ∧
        (w / s ^ 2).Coprime Δ ∧ w / s ^ 2 ≤ K := by
      by_contra hn
      simp [hn] at hne
    exact ⟨w / s ^ 2, s, hc.2.1, (Nat.mem_divisors.mp hs).1,
      (Nat.mul_div_cancel' hc.1).symm⟩
  · exact (hb rfl).elim

theorem mainRemainder_factors {K Δ w : ℕ} (h : mainRemainder K Δ w ≠ 0) :
    ∃ r s : ℕ, Squarefree r ∧ s ∣ Δ ∧ w = s ^ 2 * r := by
  by_cases ha : truncatedMainAlpha K Δ w = 0
  · apply truncatedMainBeta_factors (K := K)
    intro hb
    exact h (by simp [mainRemainder, ha, hb])
  · exact truncatedMainAlpha_factors ha

theorem norm_mainRemainder_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K Δ w : ℕ), 0 < Δ →
      ‖(mainRemainder K Δ w : ℂ)‖ ≤ C * (Δ : ℝ) ^ ε := by
  obtain ⟨C, hC, hdiv⟩ := Ostmann.Arithmetic.divisors_card_le_rpow ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro K Δ w hΔ
  have hcoeff : ‖(mainRemainder K Δ w : ℂ)‖ ≤ 2 * (Δ.divisors.card : ℝ) := by
    simpa only [Complex.norm_intCast, ← Int.cast_abs, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast] using (show ((|mainRemainder K Δ w| : ℤ) : ℝ) ≤
        ((2 * (Δ.divisors.card : ℤ) : ℤ) : ℝ) from by exact_mod_cast abs_mainRemainder_le K Δ w)
  calc
    _ ≤ 2 * (Δ.divisors.card : ℝ) := hcoeff
    _ ≤ 2 * (C * (Δ : ℝ) ^ ε) := mul_le_mul_of_nonneg_left (hdiv Δ hΔ) (by norm_num)
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
