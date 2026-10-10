import OAI.NumberTheory.EgyptianFractions.SecondMomentAssembly
import OAI.NumberTheory.EgyptianFractions.FiniteExposureAverage

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

theorem norm_expect_sq_eq_expect_pairs {I : Type*} [Fintype I] (z : I → ℂ) :
    ‖𝔼 i, z i‖ ^ 2 = 𝔼 ij : I × I, (z ij.1 * star (z ij.2)).re := by
  simp only [Fintype.expect_eq_sum_div_card, norm_div, norm_natCast]
  rw [div_pow, norm_sum_sq_eq_sum_pair]
  simp only [Fintype.card_prod, Nat.cast_mul, pow_two]

theorem uniform_second_moment_identity {Ω I : Type*} [Fintype Ω] [Fintype I]
    (z : Ω → I → ℂ) :
    (𝔼 ω, ‖𝔼 i, z ω i‖ ^ 2) =
      𝔼 ij : I × I, (𝔼 ω, z ω ij.1 * star (z ω ij.2)).re := by
  simp_rw [norm_expect_sq_eq_expect_pairs]
  rw [Finset.expect_comm]
  congr 1
  funext ij
  exact (map_expect (Complex.reCLM.toLinearMap.restrictScalars ℚ≥0) (fun ω => z ω ij.1 * star (z ω ij.2)) Finset.univ).symm

/-- Uniform finite-average version of the Hamming second-moment reduction. -/
theorem uniform_boolean_second_moment_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (m : ℕ) (z : Ω → (Fin m → Bool) → ℂ)
    (hz : ∀ ω i, ‖z ω i‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ i j, (m : ℝ) / 4 ≤ (hammingDist i j : ℝ) →
      ‖𝔼 ω, z ω i * star (z ω j)‖ ≤ δ) :
    (𝔼 ω, ‖𝔼 i, z ω i‖ ^ 2) ≤ Real.exp (-(m : ℝ) / 16) + δ := by
  classical
  let E := Finset.univ.filter (fun ij : (Fin m → Bool) × (Fin m → Bool) =>
    (hammingDist ij.1 ij.2 : ℝ) < (m : ℝ) / 4)
  have hall (i j : Fin m → Bool) : ‖𝔼 ω, z ω i * star (z ω j)‖ ≤ 1 := by
    calc
      _ ≤ 𝔼 ω, ‖z ω i * star (z ω j)‖ := RCLike.norm_expect_le (K := ℂ)
      _ ≤ 𝔼 _ω : Ω, (1 : ℝ) := by
        apply Finset.expect_le_expect
        intro ω hω
        rw [norm_mul, norm_star]
        nlinarith [hz ω i, hz ω j, norm_nonneg (z ω i), norm_nonneg (z ω j)]
      _ = 1 := Fintype.expect_const 1
  have hexc : (E.card : ℝ) ≤ (4 : ℝ) ^ m * Real.exp (-(m : ℝ) / 16) :=
    hamming_exception_count m
  have hcard : (Fintype.card ((Fin m → Bool) × (Fin m → Bool)) : ℝ) = (4 : ℝ) ^ m := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]
    norm_num
  rw [uniform_second_moment_identity]
  calc
    (𝔼 ij : (Fin m → Bool) × (Fin m → Bool),
        (𝔼 ω, z ω ij.1 * star (z ω ij.2)).re) ≤
        𝔼 ij : (Fin m → Bool) × (Fin m → Bool),
          ((if ij ∈ E then 1 else 0) + δ : ℝ) := by
      apply Finset.expect_le_expect
      intro ij hij
      by_cases hb : ij ∈ E
      · simp only [ite_eq_left hb]
        exact (Complex.re_le_norm _).trans ((hall _ _).trans (by linarith))
      · simp only [ite_eq_right hb, zero_add]
        apply (Complex.re_le_norm _).trans (hgood _ _ ?_)
        simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hb
    _ = (E.card : ℝ) / (4 : ℝ) ^ m + δ := by
      rw [Finset.expect_add_distrib, expect_finset_indicator, Fintype.expect_const, hcard]
    _ ≤ Real.exp (-(m : ℝ) / 16) + δ := by
      have hdiv : (E.card : ℝ) / (4 : ℝ) ^ m ≤ Real.exp (-(m : ℝ) / 16) :=
        (div_le_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hexc)
      linarith

/-- Uniform-mean final random estimate, directly matching the second moment
of the sampled Boolean-product exponential average. -/
theorem uniform_boolean_random_second_moment_bound {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (m : ℕ) (V : ℝ)
    (z : Ω → (Fin m → Bool) → ℂ) (hz : ∀ ω i, ‖z ω i‖ ≤ 1)
    (hlarge : 50 ≤ min (m : ℝ) V)
    (hgood : ∀ i j, (m : ℝ) / 4 ≤ (hammingDist i j : ℝ) →
      ‖𝔼 ω, z ω i * star (z ω j)‖ ≤ Real.exp (-V / 20) + Real.exp (-V / 5)) :
    (𝔼 ω, ‖𝔼 i, z ω i‖ ^ 2) ≤ Real.exp (-min (m : ℝ) V / 100) := by
  have h := uniform_boolean_second_moment_bound m z hz
    (Real.exp (-V / 20) + Real.exp (-V / 5)) (by positivity) hgood
  exact h.trans (by simpa only [add_assoc] using
    random_second_moment_absorption (m : ℝ) V hlarge)

end Problem337

end

end OAI
