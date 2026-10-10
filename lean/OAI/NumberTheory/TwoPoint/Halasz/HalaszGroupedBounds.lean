import OAI.NumberTheory.TwoPoint.Halasz.HalaszBandWeights
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTripleEstimate

namespace OAI

/-! The complementary trivial estimate for a logarithmic prime band.
Together with the Perron estimate it produces the minimum summed later. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

noncomputable def halaszGroupedDouble (f : ℕ → ℂ) (N : ℕ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, (Real.log (p : ℝ) : ℂ) * f p *
    (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))

lemma halasz_prime_convolution_trivial (f : ℕ → ℂ) (hf : OneBounded f)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖halaszPrimeConvolution f N‖ ≤ (N : ℝ) * (Real.log N + halaszMertensConstant) := by
  have hp := halasz_prime_set_bound f hf N ((Icc 1 N).filter Nat.Prime)
    (fun p hp => (mem_filter.mp hp).2)
  have hs : (Icc 1 N).filter Nat.Prime = sievePrimesUpTo (N : ℝ) := by
    ext p
    simp only [sievePrimesUpTo, Nat.floor_natCast, mem_filter, mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩⟩
  change ‖halaszPrimeConvolution f N‖ ≤ _ at hp
  rw [hs] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left
    (halasz_prime_prefix_mass_le (by exact_mod_cast hN)) (Nat.cast_nonneg _))

lemma halasz_prime_convolution_div_log (f : ℕ → ℂ) (hf : OneBounded f)
    {M : ℕ} {y : ℝ} (hy : 2 ≤ y) (hMy : (M : ℝ) ≤ y) :
    ‖halaszPrimeConvolution f M / (Real.log y : ℂ)‖ ≤
      (1 + halaszMertensConstant / Real.log 2) * y := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hly : 0 < Real.log y := htwo.trans_le hlog
  have hMertens := halaszMertensConstant_nonneg
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hly]
  by_cases hM : M = 0
  · subst M
    simp only [halaszPrimeConvolution, Icc_eq_empty_of_lt (by omega : 0 < 1),
      filter_empty, sum_empty, norm_zero, zero_div]
    positivity
  · have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
    have hLM : Real.log (M : ℝ) ≤ Real.log y :=
      Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hM)) hMy
    calc
      _ ≤ ((M : ℝ) * (Real.log M + halaszMertensConstant)) / Real.log y :=
        div_le_div_of_nonneg_right (halasz_prime_convolution_trivial f hf hM1) hly.le
      _ ≤ (y * (Real.log y + halaszMertensConstant)) / Real.log y := by
        apply div_le_div_of_nonneg_right _ hly.le
        exact mul_le_mul hMy (add_le_add hLM le_rfl)
          (add_nonneg (Real.log_nonneg (by exact_mod_cast hM1)) hMertens) (by linarith)
      _ = (1 + halaszMertensConstant / Real.log y) * y := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact add_le_add le_rfl (div_le_div_of_nonneg_left hMertens htwo hlog)

theorem halasz_grouped_double_trivial : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ → ℂ), OneBounded f → ∀ (N : ℕ) (v : ℝ), 0 < N → Real.log 2 ≤ v →
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧
      v ≤ Real.log ((N : ℝ) / p) ∧ Real.log ((N : ℝ) / p) < 2 * v) →
      ‖halaszGroupedDouble f N P‖ ≤ C * N * v := by
  let K := 1 + halaszMertensConstant / Real.log 2
  let L := 1 + 2 * halaszMertensConstant / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM := halaszMertensConstant_nonneg
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨K * L, mul_pos hK hL, ?_⟩
  intro f hf N v hN hv P hP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hm := halasz_log_band_mass_linear hN0 hv P hP
  have hp (p : ℕ) (hp : p ∈ P) :
      ‖(Real.log (p : ℝ) : ℂ) * f p *
        (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))‖ ≤
        K * N * (Real.log (p : ℝ) / p) := by
    have hprime := (hP p hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hy0 : 0 < (N : ℝ) / p := div_pos hN0 hp0
    have hy : (2 : ℝ) ≤ (N : ℝ) / p :=
      (Real.log_le_log_iff (by norm_num) hy0).mp (hv.trans (hP p hp).2.1)
    have hquot : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self N p
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le))]
    calc
      _ ≤ Real.log (p : ℝ) * 1 * (K * ((N : ℝ) / p)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf p hprime.pos) (by positivity))
          (halasz_prime_convolution_div_log f hf hy hquot) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [K]; ring
  calc
    _ ≤ ∑ p ∈ P, ‖(Real.log (p : ℝ) : ℂ) * f p *
        (halaszPrimeConvolution f (N / p) / (Real.log ((N : ℝ) / p) : ℂ))‖ := norm_sum_le _ _
    _ ≤ K * N * ∑ p ∈ P, Real.log (p : ℝ) / p := by rw [mul_sum]; exact sum_le_sum hp
    _ ≤ K * N * (L * v) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
