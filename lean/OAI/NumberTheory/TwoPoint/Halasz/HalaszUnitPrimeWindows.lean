import OAI.NumberTheory.TwoPoint.Halasz.HalaszTranslatedMeanSquare
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass

namespace OAI

/-! A fixed-width mean square for every finite prime set. The finitely many
primes below the sieve threshold cost only an absolute constant. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_prime_fixed_rows : ∃ R B : ℝ, 0 < R ∧ 2 ≤ B ∧
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ u : ℝ,
      (∑ p ∈ P, (Real.log (p : ℝ) / p) *
        (2 * B / (1 + B ^ 2 * (Real.log (p : ℝ) - u) ^ 2))) ≤ R := by
  obtain ⟨C, B, hC, hB, hwindow⟩ := halasz_prime_windows_above_square
  let M := Real.log (B ^ 2) + halaszMertensConstant
  have hBp : 0 < B := by linarith
  have hB2 : 1 ≤ B ^ 2 := by nlinarith
  have hM : 0 ≤ M := add_nonneg (Real.log_nonneg hB2) halaszMertensConstant_nonneg
  refine ⟨16 * C + 2 * B * M, B, by positivity, hB, ?_⟩
  intro P hP u
  let L := P.filter (fun p : ℕ => B ^ 2 ≤ (p : ℝ))
  let S := P \ L
  let w := fun p : ℕ => Real.log (p : ℝ) / p
  let K := fun p : ℕ => 2 * B / (1 + B ^ 2 * (Real.log (p : ℝ) - u) ^ 2)
  have hLP : L ⊆ P := filter_subset _ _
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ w p :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)
  have hlarge : ∑ p ∈ L, w p * K p ≤ 16 * C := by
    exact halasz_frequency_row_of_windows L (fun p => Real.log (p : ℝ)) w u hBp hC.le
      (fun p hp => hw p (hLP hp))
      (hwindow B L le_rfl (fun p hp => ⟨hP p (hLP hp), (mem_filter.mp hp).2⟩))
  have hsmall : ∑ p ∈ S, w p ≤ M := by
    have hsub : S ⊆ sievePrimesUpTo (B ^ 2) := by
      intro p hp
      obtain ⟨hpP, hpL⟩ := mem_sdiff.mp hp
      have hpB : (p : ℝ) < B ^ 2 := by
        by_contra! hn
        exact hpL (mem_filter.mpr ⟨hpP, hn⟩)
      exact mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff (by positivity)).mpr hpB.le), hP p hpP⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast (sievePrimesUpTo_prime _ p hp).one_le))
        (Nat.cast_nonneg _))).trans (halasz_prime_prefix_mass_le hB2)
  have hK (p : ℕ) : K p ≤ 2 * B := by
    apply div_le_self (by positivity)
    nlinarith [mul_nonneg (sq_nonneg B) (sq_nonneg (Real.log (p : ℝ) - u))]
  have hsmallrow : ∑ p ∈ S, w p * K p ≤ 2 * B * M := by
    calc
      _ ≤ ∑ p ∈ S, w p * (2 * B) :=
        sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hK p) (hw p (mem_sdiff.mp hp).1))
      _ = 2 * B * ∑ p ∈ S, w p := by rw [← sum_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
  have he : (∑ p ∈ P, w p * K p) = (∑ p ∈ L, w p * K p) + ∑ p ∈ S, w p * K p := by
    dsimp [S]
    rw [sum_sdiff_eq_sub hLP]
    ring
  change (∑ p ∈ P, w p * K p) ≤ _
  rw [he]
  exact add_le_add hlarge hsmallrow

/-- The unit-interval prime mean square, with no lower prime cutoff. -/
theorem halasz_prime_mean_square_unit : ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ (a : ℕ → ℂ) (u : ℝ),
      (∫ t in (u - 1 / 2)..(u + 1 / 2),
        ‖mrtExponentialPolynomial P
          (fun p => a p * ((Real.log (p : ℝ) / p : ℝ) : ℂ))
          (fun p => -Real.log (p : ℝ)) t‖ ^ 2) ≤
        C * ∑ p ∈ P, ‖a p‖ ^ 2 * (Real.log (p : ℝ) / p) := by
  obtain ⟨R, B, hR, hB, hrows⟩ := halasz_prime_fixed_rows
  refine ⟨Real.exp 1 * R, by positivity, ?_⟩
  intro P hP a u
  let w := fun p : ℕ => Real.log (p : ℝ) / p
  let freq := fun p : ℕ => -Real.log (p : ℝ)
  let phase := fun p => Complex.exp (((freq p * u : ℝ) : ℂ) * Complex.I)
  let D := mrtExponentialPolynomial P (fun p => a p * (w p : ℂ)) freq
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ w p :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)
  have hr : ∀ p ∈ P,
      (∑ q ∈ P, w q * (2 * B / (1 + B ^ 2 * (freq p - freq q) ^ 2))) ≤ R := by
    intro p _
    convert hrows P hP (Real.log (p : ℝ)) using 1
    apply sum_congr rfl
    intro q _
    dsimp [freq]
    ring
  have hm := halasz_mean_square_of_weighted_rows P (fun p => a p * phase p) w freq
    (by linarith : 0 < B) hw hr
  have he (t : ℝ) : mrtExponentialPolynomial P (fun p => (a p * phase p) * (w p : ℂ))
      freq t = D (t + u) := by
    dsimp only [D]
    rw [← halasz_polynomial_translate]
    unfold mrtExponentialPolynomial
    apply sum_congr rfl
    intro p _
    dsimp [phase]
    ring
  have hp (p : ℕ) : ‖a p * phase p‖ = ‖a p‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  simp_rw [he, hp] at hm
  have ht := intervalIntegral.integral_comp_add_right (fun t => ‖D t‖ ^ 2) u
    (a := -B) (b := B)
  rw [ht] at hm
  have hmono : (∫ t in (u - 1 / 2)..(u + 1 / 2), ‖D t‖ ^ 2) ≤
      ∫ t in (-B + u)..(B + u), ‖D t‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun t => sq_nonneg _))
    exact ((halasz_polynomial_continuous P _ freq).norm.pow 2).intervalIntegrable _ _
  exact hmono.trans hm

end TwoPointCorrelations

end OAI
