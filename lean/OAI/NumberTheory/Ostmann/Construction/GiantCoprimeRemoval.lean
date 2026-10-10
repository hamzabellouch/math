import Mathlib.Data.Nat.Factorization.Basic
import OAI.NumberTheory.Ostmann.Construction.GiantDiscreteTransport

namespace OAI

/-! # Removing only the top-giant coprimality test under the original laws -/

namespace Ostmann
open scoped BigOperators Classical

theorem weighted_coprime_removal_bound (P R : Finset ℕ) (ν μ : ℕ → ℝ)
    (hν : ∀ p ∈ P, 0 ≤ ν p) (hμ : ∀ r ∈ R, 0 ≤ μ r)
    (F : ℕ → ℕ → ℂ) (K : ℝ) (hF : ∀ p ∈ P, ∀ r ∈ R, ‖F p r‖ ≤ K) :
    ‖(∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * (if p.Coprime r then F p r else 0)) -
      ∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * F p r‖ ≤
      ∑ r ∈ R, μ r * (K * ∑ p ∈ P, if p.Coprime r then 0 else ν p) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ R, ‖(μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * (if p.Coprime r then F p r else 0) -
        (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * F p r‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro r hr
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ r hr)]
      apply mul_le_mul_of_nonneg_left _ (hμ r hr)
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
      by_cases hc : p.Coprime r
      · rw [ite_eq_left hc, ite_eq_left hc, sub_self, norm_zero, mul_zero]
      · simp only [hc, ite_false, mul_zero, zero_sub, norm_neg, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg (hν p hp)]
        exact (mul_le_mul_of_nonneg_left (hF p hp r hr) (hν p hp)).trans_eq (mul_comm _ _)

theorem weighted_prime_coprime_removal (P R : Finset ℕ) (ν μ : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hν : ∀ p ∈ P, 0 ≤ ν p) (hμ : ∀ r ∈ R, 0 ≤ μ r)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ p ∈ P, ν p ≤ α)
    (F : ℕ → ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ p ∈ P, ∀ r ∈ R, ‖F p r‖ ≤ K) :
    ‖(∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * (if p.Coprime r then F p r else 0)) -
      ∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * F p r‖ ≤ K * α * ∑ r ∈ R, μ r := by
  refine (weighted_coprime_removal_bound P R ν μ hν hμ F K hF).trans ?_
  calc
    _ ≤ ∑ r ∈ R, μ r * (K * α) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (hμ r hr)
      apply mul_le_mul_of_nonneg_left _ hK
      have he : (∑ p ∈ P, if p.Coprime r then 0 else ν p) =
          ∑ p ∈ P, if p = r then ν p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases he : p = r
        · have hc : ¬ p.Coprime r := fun hc => (Nat.coprime_primes (hP p hp) (hR r hr)).mp hc he
          rw [ite_eq_right hc, ite_eq_left he]
        · have hc := (Nat.coprime_primes (hP p hp) (hR r hr)).mpr he
          rw [ite_eq_left hc, ite_eq_right he]
      rw [he]
      by_cases hrP : r ∈ P
      · simpa [hrP] using hmax r hrP
      · simpa [hrP] using hα
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem integer_bad_coprime_mass (P : Finset ℕ) (ν : ℕ → ℝ)
    (N r : ℕ) (hr : r.Prime) (hpos : ∀ p ∈ P, 0 < p) (hN : ∀ p ∈ P, p ≤ N)
    (β : ℝ) (hβ : 0 ≤ β) (hmax : ∀ p ∈ P, ν p ≤ β) :
    (∑ p ∈ P, if p.Coprime r then 0 else ν p) ≤ β * (N / r : ℕ) := by
  have hs : P.filter (fun p => ¬ p.Coprime r) ⊆
      (Finset.range (N + 1)).filter (fun p => p ≠ 0 ∧ r ∣ p) := by
    intro p hp
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hN p hp; omega),
      Nat.ne_of_gt (hpos p hp), hr.dvd_iff_not_coprime.mpr (by simpa only [Nat.coprime_comm] using hc)⟩
  have hcard : (P.filter fun p => ¬ p.Coprime r).card ≤ N / r := by
    exact (Finset.card_le_card hs).trans_eq (Nat.card_multiples' N r)
  calc
    _ = ∑ p ∈ P.filter (fun p => ¬ p.Coprime r), ν p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hc : p.Coprime r <;> simp [hc]
    _ ≤ ∑ _p ∈ P.filter (fun p => ¬ p.Coprime r), β :=
      Finset.sum_le_sum fun p hp => hmax p (Finset.mem_filter.mp hp).1
    _ = ((P.filter fun p => ¬ p.Coprime r).card : ℝ) * β := by simp
    _ ≤ (N / r : ℕ) * β := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hβ
    _ = _ := mul_comm _ _

theorem weighted_integer_prime_coprime_removal (P R : Finset ℕ) (ν μ : ℕ → ℝ)
    (N : ℕ) (hR : ∀ r ∈ R, r.Prime) (hpos : ∀ p ∈ P, 0 < p) (hN : ∀ p ∈ P, p ≤ N)
    (hν : ∀ p ∈ P, 0 ≤ ν p) (hμ : ∀ r ∈ R, 0 ≤ μ r)
    (β : ℝ) (hβ : 0 ≤ β) (hmax : ∀ p ∈ P, ν p ≤ β)
    (F : ℕ → ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hF : ∀ p ∈ P, ∀ r ∈ R, ‖F p r‖ ≤ K) :
    ‖(∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * (if p.Coprime r then F p r else 0)) -
      ∑ r ∈ R, (μ r : ℂ) * ∑ p ∈ P, (ν p : ℂ) * F p r‖ ≤
      K * β * N * ∑ r ∈ R, μ r / r := by
  refine (weighted_coprime_removal_bound P R ν μ hν hμ F K hF).trans ?_
  calc
    _ ≤ ∑ r ∈ R, μ r * (K * (β * ((N : ℝ) / r))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (hμ r hr)
      apply mul_le_mul_of_nonneg_left _ hK
      exact (integer_bad_coprime_mass P ν N r (hR r hr) hpos hN β hβ hmax).trans
        (mul_le_mul_of_nonneg_left Nat.cast_div_le hβ)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring

end Ostmann

end OAI
