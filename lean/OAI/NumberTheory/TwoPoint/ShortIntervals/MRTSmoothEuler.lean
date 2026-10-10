import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTEulerProducts
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalRamare
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare
import Mathlib.NumberTheory.EulerProduct.Basic

namespace OAI

/-! The finite-prime smooth Euler product on Re(s)=1.  Finite prime
support makes the series absolutely convergent even on this line; the
geometric local factors therefore give the actual analytic series to
which the pretentious-distance estimate applies. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical ComplexConjugate

lemma mrt_line_one_euler_term (F : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    LSeries.term F (1 + (t : ℂ) * Complex.I) n = mrtPrimeEulerTerm F t n := by
  have he : conj (mrtArchimedeanTwist t n) =
      Complex.exp (((-Real.log (n : ℝ)) * t : ℝ) * Complex.I) := by
    rw [mrtArchimedeanTwist, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [mrt_line_one_term F hn t, mrtPrimeEulerTerm, he]
  ring

lemma mrt_LSeries_term_pow (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    LSeries.term F s (p ^ k) = (LSeries.term F s p) ^ k := by
  induction k with
  | zero => simp [LSeries.term, hF1]
  | succ k ih =>
    calc
      _ = LSeries.term F s (p ^ k * p) := by rw [pow_succ]
      _ = LSeries.term F s (p ^ k) * LSeries.term F s p :=
        mrt_LSeries_term_mul F hF s (pow_pos hp k) hp
      _ = _ := by rw [ih, pow_succ]

lemma mrt_LSeries_term_coprime_mul (F : ℕ → ℂ)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (s : ℂ) {m n : ℕ} (_h : m.Coprime n) :
    LSeries.term F s (m * n) = LSeries.term F s m * LSeries.term F s n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  exact mrt_LSeries_term_mul F hF s (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

lemma mrt_prime_euler_norm_lt_one (F : ℕ → ℂ) (hF : OneBounded F)
    (t : ℝ) {p : ℕ} (hp : p.Prime) : ‖mrtPrimeEulerTerm F t p‖ < 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ (1 : ℝ) / p := mrtPrimeEulerTerm_norm_le F t hp.pos (hF p hp.pos)
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    _ < 1 := by norm_num

/-- The actual smooth L-series is absolutely summable and equals its
finite Euler product on the boundary line `Re(s)=1`. -/
theorem mrt_smooth_euler_product (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) :
    Summable (fun n : Nat.smoothNumbers (N + 1) =>
      ‖LSeries.term F (1 + (t : ℂ) * Complex.I) n‖) ∧
    HasSum (fun n : Nat.smoothNumbers (N + 1) =>
      LSeries.term F (1 + (t : ℂ) * Complex.I) n)
      (∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹) := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have h1 : LSeries.term F s 1 = 1 := by simp [LSeries.term, hF1]
  have hlocal (p : ℕ) (hp : p.Prime) (k : ℕ) :
      LSeries.term F s (p ^ k) = (mrtPrimeEulerTerm F t p) ^ k := by
    rw [mrt_LSeries_term_pow F hF1 hF s hp.pos k,
      mrt_line_one_euler_term F hp.ne_zero t]
  have hnorm : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ => ‖LSeries.term F s (p ^ k)‖) := by
    intro p hp
    simpa only [hlocal p hp, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg _)
        (mrt_prime_euler_norm_lt_one F hFb t hp))
  obtain ⟨hs, he⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    h1 (fun {_ _} h => mrt_LSeries_term_coprime_mul F hF s h) hnorm (N + 1)
  have hprod : (∏ p ∈ (N + 1).primesBelow, ∑' k : ℕ, LSeries.term F s (p ^ k)) =
      ∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm F t p)⁻¹ := by
    change (∏ p ∈ primesUpTo N, ∑' k : ℕ, LSeries.term F s (p ^ k)) = _
    apply prod_congr rfl
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2
    calc
      _ = ∑' k : ℕ, (mrtPrimeEulerTerm F t p) ^ k := tsum_congr (hlocal p hprime)
      _ = _ := (hasSum_geometric_of_norm_lt_one
        (mrt_prime_euler_norm_lt_one F hFb t hprime)).tsum_eq
  rw [hprod] at he
  exact ⟨hs, he⟩

/-- The distance saving applies to the analytic smooth series itself,
with the same finite prime-square error as its Euler product. -/
theorem mrt_smooth_euler_distance_bound (F : ℕ → ℂ) (hF1 : F 1 = 1)
    (hF : ∀ m n, 0 < m → 0 < n → F (m * n) = F m * F n)
    (hFb : OneBounded F) (N : ℕ) (t : ℝ) :
    ‖∑' n : Nat.smoothNumbers (N + 1), LSeries.term F (1 + (t : ℂ) * Complex.I) n‖ ≤
      Real.exp ((∑ p ∈ primesUpTo N, (1 : ℝ) / p) -
        squaredDistance F (mrtArchimedeanTwist t) N +
        ∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [(mrt_smooth_euler_product F hF1 hF hFb N t).2.tsum_eq]
  exact mrt_finite_euler_distance_bound F hFb t N

end TwoPointCorrelations

end OAI
