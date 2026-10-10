import OAI.NumberTheory.TwoPoint.Halasz.HalaszMixedInner
import OAI.NumberTheory.TwoPoint.Halasz.HalaszGroupedBounds

namespace OAI

/-! Trivial estimates for the mixed prime convolution. The underlying
prime values and the bounded typical cofactor are different sequences. -/

namespace TwoPointCorrelations

open Finset Complex
open scoped Classical

noncomputable def halaszMixedGrouped (G B : ℕ → ℂ) (N : ℕ) (L : ℝ)
    (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, (Real.log (p:ℝ):ℂ)*G p*
    (halaszMixedPrimeConvolution G B (N/p) L ((N/p:ℕ):ℝ)/(Real.log ((N:ℝ)/p):ℂ))

lemma halasz_mixed_prime_term_bound (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) (N p : ℕ) (hp : p.Prime) :
    ‖(Real.log (p:ℝ):ℂ)*G p*(∑ m ∈ Icc 1 (N/p), B m)‖ ≤
      (N:ℝ)*(Real.log (p:ℝ)/p) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hdiv : ((N/p:ℕ):ℝ) ≤ (N:ℝ)/p := by
    apply (le_div_iff₀ hp0).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  calc
    _ ≤ Real.log (p:ℝ)*1*((N/p:ℕ):ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hG p hp.pos) hlog)
        (halasz_bounded_prefix_norm B hB (N/p)) (norm_nonneg _) (by positivity)
    _ ≤ Real.log (p:ℝ)*((N:ℝ)/p) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdiv hlog
    _ = _ := by ring

lemma halasz_mixed_convolution_trivial (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) {N : ℕ} (hN : 1 ≤ N) (L : ℝ) :
    ‖halaszMixedPrimeConvolution G B N L N‖ ≤
      (N:ℝ)*(Real.log N+halaszMertensConstant) := by
  unfold halaszMixedPrimeConvolution
  calc
    _ ≤ (N:ℝ)*∑ p ∈ mrtPrimeBand L N, Real.log (p:ℝ)/p := by
      rw [mul_sum]
      exact (norm_sum_le _ _).trans (sum_le_sum (fun p hp =>
        halasz_mixed_prime_term_bound G B hG hB N p (mrtPrimeBand_prime hp)))
    _ ≤ (N:ℝ)*∑ p ∈ sievePrimesUpTo (N:ℝ), Real.log (p:ℝ)/p := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p hp _ =>
        div_nonneg (Real.log_nonneg (by exact_mod_cast
          (sievePrimesUpTo_prime (N:ℝ) p hp).one_le)) (Nat.cast_nonneg p))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (halasz_prime_prefix_mass_le (by exact_mod_cast hN)) (Nat.cast_nonneg N)

lemma halasz_mixed_convolution_div_log (G B : ℕ → ℂ) (hG : OneBounded G)
    (hB : OneBounded B) (L : ℝ) {M : ℕ} {y : ℝ} (hy : 2 ≤ y) (hMy : (M:ℝ) ≤ y) :
    ‖halaszMixedPrimeConvolution G B M L M/(Real.log y:ℂ)‖ ≤
      (1+halaszMertensConstant/Real.log 2)*y := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hly : 0 < Real.log y := htwo.trans_le hlog
  have hC := halaszMertensConstant_nonneg
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hly]
  by_cases hM : M = 0
  · subst M
    norm_num only [Nat.cast_zero]
    have he : mrtPrimeBand L 0 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hle := sievePrimesUpTo_le 0 (by norm_num) p (mem_sdiff.mp hp).1
      have hpos : (0:ℝ)<p := by exact_mod_cast (mrtPrimeBand_prime hp).pos
      linarith
    rw [show halaszMixedPrimeConvolution G B 0 L (0:ℝ) = 0 by
      simp only [halaszMixedPrimeConvolution,he,sum_empty]]
    rw [norm_zero,zero_div]
    positivity
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
  have hLM : Real.log (M:ℝ) ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast (Nat.pos_of_ne_zero hM)) hMy
  calc
    _ ≤ ((M:ℝ)*(Real.log M+halaszMertensConstant))/Real.log y :=
      div_le_div_of_nonneg_right (halasz_mixed_convolution_trivial G B hG hB hM1 L) hly.le
    _ ≤ (y*(Real.log y+halaszMertensConstant))/Real.log y := by
      apply div_le_div_of_nonneg_right _ hly.le
      exact mul_le_mul hMy (add_le_add hLM le_rfl)
        (add_nonneg (Real.log_nonneg (by exact_mod_cast hM1)) hC) (by linarith)
    _ = (1+halaszMertensConstant/Real.log y)*y := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (div_le_div_of_nonneg_left hC htwo hlog)) (by linarith)

theorem halasz_mixed_grouped_trivial : ∃ C : ℝ, 0 < C ∧
    ∀ G B : ℕ → ℂ, OneBounded G → OneBounded B → ∀ (N : ℕ) (L v : ℝ),
      0 < N → Real.log 2 ≤ v → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ v ≤ Real.log ((N:ℝ)/p) ∧ Real.log ((N:ℝ)/p) < 2*v) →
      ‖halaszMixedGrouped G B N L P‖ ≤ C*N*v := by
  let K := 1+halaszMertensConstant/Real.log 2
  let D := 1+2*halaszMertensConstant/Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC := halaszMertensConstant_nonneg
  have hK : 0 < K := by dsimp [K]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro G B hG hB N L v hN hv P hP
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hm := halasz_log_band_mass_linear hN0 hv P hP
  have hp (p:ℕ) (hp:p∈P) :
      ‖(Real.log (p:ℝ):ℂ)*G p*
        (halaszMixedPrimeConvolution G B (N/p) L ((N/p:ℕ):ℝ)/(Real.log ((N:ℝ)/p):ℂ))‖ ≤
        K*N*(Real.log (p:ℝ)/p) := by
    have hprime := (hP p hp).1
    have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
    have hy0 : 0 < (N:ℝ)/p := div_pos hN0 hp0
    have hy : (2:ℝ) ≤ (N:ℝ)/p :=
      (Real.log_le_log_iff (by norm_num) hy0).mp (hv.trans (hP p hp).2.1)
    have hquot : ((N/p:ℕ):ℝ) ≤ (N:ℝ)/p := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self N p
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le))]
    calc
      _ ≤ Real.log (p:ℝ)*1*(K*((N:ℝ)/p)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hG p hprime.pos) (by positivity))
          (halasz_mixed_convolution_div_log G B hG hB L hy hquot) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [K]; ring
  calc
    _ ≤ ∑ p ∈ P, ‖(Real.log (p:ℝ):ℂ)*G p*
        (halaszMixedPrimeConvolution G B (N/p) L ((N/p:ℕ):ℝ)/(Real.log ((N:ℝ)/p):ℂ))‖ := norm_sum_le _ _
    _ ≤ K*N*∑ p ∈ P, Real.log (p:ℝ)/p := by rw [mul_sum]; exact sum_le_sum hp
    _ ≤ K*N*(D*v) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
