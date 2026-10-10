import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLiouvilleDistance

namespace OAI

/-! The finite character Euler product and the real prime sum differ,
after taking log norm, by an absolute prime-square error. This reduces
the Liouville prime-tail estimate to a genuine Euler-product lower bound. -/

namespace TwoPointCorrelations

open Finset
open scoped ComplexConjugate Classical

lemma mrt_local_euler_log_error {z : ℂ} (hz : ‖z‖≤1/2) :
    |Real.log ‖(1-z)⁻¹‖-z.re| ≤ ‖z‖^2 := by
  have hz1 : ‖z‖<1 := by linarith
  have hi : (1-‖z‖)⁻¹≤2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by linarith : 0<1-‖z‖)).mpr
    linarith
  have hr : ‖Complex.log (1-z)⁻¹-z‖≤‖z‖^2 := by
    apply (Complex.norm_log_one_sub_inv_sub_self_le hz1).trans
    calc
      _ ≤ ‖z‖^2*2/2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hi (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  have hh := (Complex.abs_re_le_norm (Complex.log (1-z)⁻¹-z)).trans hr
  simpa only [Complex.sub_re,Complex.log_re] using hh

noncomputable def mrtCharacterPrimeEuler {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (S : Finset ℕ) : ℂ :=
  ∏ p ∈ S, (1-characterTwist χ t p/(p:ℂ))⁻¹

theorem mrt_character_euler_log_error {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (N : ℕ) (S : Finset ℕ) (hS : S⊆primesUpTo N) :
    |Real.log ‖mrtCharacterPrimeEuler χ t S‖-
      (∑ p ∈ S, characterTwist χ t p/(p:ℂ)).re| ≤ 2 := by
  let z := fun p : ℕ => characterTwist χ t p/(p:ℂ)
  have hz (p : ℕ) (hp : p∈S) : ‖z p‖≤1/(p:ℝ) := by
    dsimp only [z]
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p) (Nat.cast_nonneg p)
  have hhalf (p : ℕ) (hp : p∈S) : ‖z p‖≤1/2 := by
    have hp2 : (2:ℝ)≤p := by exact_mod_cast (mem_filter.mp (hS hp)).2.two_le
    exact (hz p hp).trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have hne (p : ℕ) (hp : p∈S) : 1-z p≠0 := by
    intro he
    have he' : z p=1 := (sub_eq_zero.mp he).symm
    have hh := hhalf p hp
    rw [he',norm_one] at hh
    norm_num at hh
  have hlog : Real.log ‖mrtCharacterPrimeEuler χ t S‖ =
      ∑ p ∈ S, Real.log ‖(1-z p)⁻¹‖ := by
    unfold mrtCharacterPrimeEuler
    rw [norm_prod]
    exact Real.log_prod (fun p hp => norm_ne_zero_iff.mpr (inv_ne_zero (hne p hp)))
  have hsq : (∑ p ∈ S, ‖z p‖^2) ≤ 2 := by
    calc
      _ ≤ ∑ p ∈ S, 1/(p:ℝ)^2 := by
        apply sum_le_sum
        intro p hp
        calc
          _ ≤ (1/(p:ℝ))^2 := pow_le_pow_left₀ (norm_nonneg _) (hz p hp) 2
          _ = _ := by rw [div_pow,one_pow]
      _ ≤ ∑ p ∈ primesUpTo N, 1/(p:ℝ)^2 :=
        sum_le_sum_of_subset_of_nonneg hS (by intros; positivity)
      _ ≤ 2 := mrt_prime_inverse_square_sum N
  rw [hlog,Complex.re_sum]
  change |(∑ p ∈ S, Real.log ‖(1-z p)⁻¹‖)-(∑ p ∈ S, (z p).re)|≤2
  rw [← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans
    ((sum_le_sum (fun p hp => mrt_local_euler_log_error (hhalf p hp))).trans hsq)

lemma mrt_character_prime_sum_ge_of_euler_log {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (N : ℕ) (S : Finset ℕ)
    (hS : S⊆primesUpTo N) (K : ℝ)
    (hlower : -K≤Real.log ‖mrtCharacterPrimeEuler χ t S‖) :
    -K-2≤(∑ p ∈ S, characterTwist χ t p/(p:ℂ)).re := by
  have hh := (abs_le.mp (mrt_character_euler_log_error χ t N S hS)).2
  linarith

end TwoPointCorrelations

end OAI
