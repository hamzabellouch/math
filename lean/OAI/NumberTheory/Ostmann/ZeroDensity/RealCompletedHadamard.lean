import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedPartialFractionLimit
import OAI.NumberTheory.Ostmann.Characters.CharacterDiskIndices
import OAI.NumberTheory.Ostmann.ZeroDensity.RealCharacterZeroConvergence
import OAI.NumberTheory.Ostmann.ZeroDensity.RealZeroReflectionPermutation

namespace OAI

/-! # The real-axis Hadamard identity from actual disk sums -/

namespace Ostmann

open Complex Filter
open scoped Topology BigOperators

noncomputable def realCharacterZeroSum (χ : PrimitiveRealCharacter) (s : ℝ) : ℝ :=
  ∑' i, realZeroKernel (s - ((realCharacterActualZeros χ).zeros i).re)
    ((realCharacterActualZeros χ).zeros i).im

theorem completed_partial_real_limit (χ : PrimitiveRealCharacter) (s : ℝ)
    (hsum : Summable (fun i => realZeroKernel (s - ((realCharacterActualZeros χ).zeros i).re)
      ((realCharacterActualZeros χ).zeros i).im)) :
    Tendsto (fun n : ℕ => (completedZeroPartialFraction χ.asComplex ((n : ℝ) + 1) (s : ℂ)).re)
      atTop (𝓝 (realCharacterZeroSum χ s)) := by
  let Z := realCharacterActualZeros χ
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh := hsum.hasSum.comp (Z.tendsto_diskIndices.comp hn)
  unfold realCharacterZeroSum
  convert hh using 1
  funext n
  rw [completedZeroPartialFraction_index_sum χ.asComplex (faithfulCharacterZeroEquiv χ.asComplex),
    Complex.re_sum]
  exact Finset.sum_congr rfl (fun i _ => realZeroKernel_complex s _)

theorem real_zero_kernel_reflection (χ : PrimitiveRealCharacter) (s : ℝ) (i : ℕ) :
    realZeroKernel (1 - s - ((realCharacterActualZeros χ).zeros i).re)
        ((realCharacterActualZeros χ).zeros i).im =
      -realZeroKernel (s - ((realCharacterActualZeros χ).zeros (realZeroIndexReflection χ i)).re)
        ((realCharacterActualZeros χ).zeros (realZeroIndexReflection χ i)).im := by
  rw [realZeroIndexReflection_zeros]
  rw [← realZeroKernel_complex s]
  have he : (s : ℂ) - (1 - (realCharacterActualZeros χ).zeros i) =
      -(((1 - s : ℝ) : ℂ) - (realCharacterActualZeros χ).zeros i) := by push_cast; ring
  rw [he, inv_neg, Complex.neg_re, neg_neg, realZeroKernel_complex]

theorem real_zero_sum_reflection (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 1 < s) (hs2 : s ≤ 2) :
    Summable (fun i => realZeroKernel (1 - s - ((realCharacterActualZeros χ).zeros i).re)
      ((realCharacterActualZeros χ).zeros i).im) ∧
      realCharacterZeroSum χ (1 - s) = -realCharacterZeroSum χ s := by
  have hp := real_character_zero_kernel_summable χ s hs hs2
  have hr := hp.comp_injective (realZeroIndexReflection χ).injective
  constructor
  · simpa only [real_zero_kernel_reflection, Function.comp_def] using hr.neg
  · unfold realCharacterZeroSum
    simp_rw [real_zero_kernel_reflection]
    rw [tsum_neg]
    congr 1
    exact (realZeroIndexReflection χ).tsum_eq
      (fun i => realZeroKernel (s - ((realCharacterActualZeros χ).zeros i).re)
        ((realCharacterActualZeros χ).zeros i).im)

/-- Reflection cancels the constant term in the canonical product. -/
theorem real_completed_hadamard_identity (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 1 < s) (hs2 : s ≤ 2) :
    realCharacterZeroSum χ s = (logDeriv χ.asComplex.completed (s : ℂ)).re +
      (1 / 2) * Real.log χ.modulus := by
  have hp := completed_partial_real_limit χ s (real_character_zero_kernel_summable χ s hs hs2)
  obtain ⟨hn, heq⟩ := real_zero_sum_reflection χ s hs hs2
  have hm := completed_partial_real_limit χ (1 - s) hn
  have hc := completed_partial_fraction_difference_tendsto χ.asComplex
    (1 - (s : ℂ)) (s : ℂ)
    (χ.asComplex.completed_ne_zero_left _ (by simp; linarith))
    (χ.asComplex.completed_ne_zero_right _ (by simp; linarith))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  have hd := hp.sub hm
  have hlim : realCharacterZeroSum χ s - realCharacterZeroSum χ (1 - s) =
      (logDeriv χ.asComplex.completed (s : ℂ) - logDeriv χ.asComplex.completed (1 - (s : ℂ))).re := by
    apply tendsto_nhds_unique hd
    simpa only [Function.comp_def, Complex.sub_re, Complex.ofReal_sub, Complex.ofReal_one] using hr
  rw [heq, χ.completed_logDeriv_reflection (s : ℂ) (by simp; linarith)] at hlim
  simp only [Complex.sub_re, Complex.neg_re, Complex.log_re, Complex.norm_natCast] at hlim
  linarith

end Ostmann

end OAI
