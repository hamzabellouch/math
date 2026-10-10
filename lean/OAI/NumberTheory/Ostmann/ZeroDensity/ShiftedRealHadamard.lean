import OAI.NumberTheory.Ostmann.ZeroDensity.ActualRealZeroExpansion

namespace OAI

/-! # Real parts of the Hadamard identity off the real axis -/

namespace Ostmann

open Complex Filter
open scoped Topology BigOperators

theorem realZeroKernel_complex_sub (s ρ : ℂ) :
    ((s - ρ)⁻¹).re = realZeroKernel (s.re - ρ.re) (s.im - ρ.im) := by
  simp only [Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    realZeroKernel, pow_two]

theorem inverse_square_shift_bound (y t : ℝ) :
    ((1 + |t - y|) ^ 2)⁻¹ ≤ (1 + |t|) ^ 2 * ((1 + |y|) ^ 2)⁻¹ := by
  have htri : |y| ≤ |t| + |t - y| := by
    have hh := abs_add_le (t - y) (-t)
    have he : t - y + -t = -y := by ring
    rw [he, abs_neg, abs_neg] at hh
    linarith
  have hb : 1 + |y| ≤ (1 + |t|) * (1 + |t - y|) := by
    nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (t - y))]
  have hs : (1 + |y|) ^ 2 ≤ (1 + |t|) ^ 2 * (1 + |t - y|) ^ 2 := by
    calc
      _ ≤ ((1 + |t|) * (1 + |t - y|)) ^ 2 := by gcongr
      _ = _ := by ring
  have hy : 0 < (1 + |y|) ^ 2 := by positivity
  have ht : 0 < (1 + |t - y|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ ht hy]
  simpa using hs

noncomputable def shiftedRealCharacterZeroSum (χ : PrimitiveRealCharacter) (s : ℂ) : ℝ :=
  ∑' i, ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re

theorem shifted_real_zero_summable (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    Summable (fun i => ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re) := by
  let Z := realCharacterActualZeros χ
  have hh := character_zero_inverse_square_summable χ.asComplex
  let C := 8 + 4 * (s.re - 1)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply Summable.of_nonneg_of_le
    (fun i => by rw [realZeroKernel_complex_sub]; exact realZeroKernel_nonneg (by linarith [(Z.in_strip i).2]))
    (fun i => ?_) (hh.mul_left (C * (1 + |s.im|) ^ 2))
  rw [realZeroKernel_complex_sub]
  calc
    _ ≤ C * ((1 + |s.im - (Z.zeros i).im|) ^ 2)⁻¹ :=
      real_zero_kernel_square_bound _ _ (s.re - 1) (by linarith)
        (by linarith [(Z.in_strip i).2]) (by linarith [(Z.in_strip i).1])
    _ ≤ C * ((1 + |s.im|) ^ 2 * ((1 + |(Z.zeros i).im|) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left (inverse_square_shift_bound _ _) hC
    _ = _ := by dsimp [Z, realCharacterActualZeros]; ring

theorem shifted_completed_partial_real_limit (χ : PrimitiveRealCharacter) (s : ℂ)
    (hsum : Summable (fun i => ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re)) :
    Tendsto (fun n : ℕ => (completedZeroPartialFraction χ.asComplex ((n : ℝ) + 1) s).re)
      atTop (𝓝 (shiftedRealCharacterZeroSum χ s)) := by
  let Z := realCharacterActualZeros χ
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh := hsum.hasSum.comp (Z.tendsto_diskIndices.comp hn)
  unfold shiftedRealCharacterZeroSum
  convert hh using 1
  funext n
  rw [completedZeroPartialFraction_index_sum χ.asComplex (faithfulCharacterZeroEquiv χ.asComplex),
    Complex.re_sum]
  rfl

theorem shifted_real_zero_reflection (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    Summable (fun i => ((1 - s - (realCharacterActualZeros χ).zeros i)⁻¹).re) ∧
      shiftedRealCharacterZeroSum χ (1 - s) = -shiftedRealCharacterZeroSum χ s := by
  have he (i : ℕ) : ((1 - s - (realCharacterActualZeros χ).zeros i)⁻¹).re =
      -((s - (realCharacterActualZeros χ).zeros (realZeroIndexReflection χ i))⁻¹).re := by
    rw [realZeroIndexReflection_zeros]
    have ha : 1 - s - (realCharacterActualZeros χ).zeros i =
        -(s - (1 - (realCharacterActualZeros χ).zeros i)) := by ring
    rw [ha, inv_neg, Complex.neg_re]
  have hsum := shifted_real_zero_summable χ s hs hs2
  constructor
  · simpa only [he, Function.comp_def] using
      (hsum.comp_injective (realZeroIndexReflection χ).injective).neg
  · unfold shiftedRealCharacterZeroSum
    simp_rw [he]
    rw [tsum_neg]
    congr 1
    exact (realZeroIndexReflection χ).tsum_eq
      (fun i => ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re)

/-- The shifted identity supplies the actual zero terms used in the
low-height zero-free-region argument. -/
theorem shifted_real_hadamard_identity (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    shiftedRealCharacterZeroSum χ s = (logDeriv χ.asComplex.completed s).re +
      (1 / 2) * Real.log χ.modulus := by
  have hp := shifted_completed_partial_real_limit χ s (shifted_real_zero_summable χ s hs hs2)
  obtain ⟨hn, heq⟩ := shifted_real_zero_reflection χ s hs hs2
  have hm := shifted_completed_partial_real_limit χ (1 - s) hn
  have hc := completed_partial_fraction_difference_tendsto χ.asComplex (1 - s) s
    (χ.asComplex.completed_ne_zero_left _ (by simp; linarith))
    (χ.asComplex.completed_ne_zero_right _ hs.le)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  have hlim : shiftedRealCharacterZeroSum χ s - shiftedRealCharacterZeroSum χ (1 - s) =
      (logDeriv χ.asComplex.completed s - logDeriv χ.asComplex.completed (1 - s)).re := by
    apply tendsto_nhds_unique (hp.sub hm)
    simpa only [Function.comp_def, Complex.sub_re] using hr
  rw [heq, χ.completed_logDeriv_reflection s hs.le] at hlim
  simp only [Complex.sub_re, Complex.neg_re, Complex.log_re, Complex.norm_natCast] at hlim
  linarith

end Ostmann

end OAI
