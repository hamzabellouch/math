import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedCharacterConjugation
import OAI.NumberTheory.Ostmann.Characters.CharacterSelfReflection
import OAI.NumberTheory.Ostmann.ZeroDensity.ShiftedRealHadamard

namespace OAI

/-! # The actual real-part Hadamard identity for complex characters -/

namespace Ostmann

open Complex Filter
open scoped Topology BigOperators ComplexConjugate

noncomputable def characterRealZeroSum (χ : PrimitiveComplexCharacter) (s : ℂ) : ℝ :=
  ∑' i, ((s - (actualCharacterZeros χ).zeros i)⁻¹).re

theorem character_real_zero_summable (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    Summable (fun i => ((s - (actualCharacterZeros χ).zeros i)⁻¹).re) := by
  let Z := actualCharacterZeros χ
  have hh := character_zero_inverse_square_summable χ
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
    _ = _ := by dsimp [Z]; ring

theorem character_completed_partial_real_limit (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hsum : Summable (fun i => ((s - (actualCharacterZeros χ).zeros i)⁻¹).re)) :
    Tendsto (fun n : ℕ => (completedZeroPartialFraction χ ((n : ℝ) + 1) s).re)
      atTop (𝓝 (characterRealZeroSum χ s)) := by
  let Z := actualCharacterZeros χ
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh := hsum.hasSum.comp (Z.tendsto_diskIndices.comp hn)
  unfold characterRealZeroSum
  convert hh using 1
  funext n
  rw [completedZeroPartialFraction_index_sum χ (faithfulCharacterZeroEquiv χ), Complex.re_sum]
  rfl

theorem character_real_zero_self_reflection (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    Summable (fun i => ((1 - conj s - (actualCharacterZeros χ).zeros i)⁻¹).re) ∧
      characterRealZeroSum χ (1 - conj s) = -characterRealZeroSum χ s := by
  have he (i : ℕ) : ((1 - conj s - (actualCharacterZeros χ).zeros i)⁻¹).re =
      -((s - (actualCharacterZeros χ).zeros (characterZeroIndexSelfReflection χ i))⁻¹).re := by
    rw [characterZeroIndexSelfReflection_zeros]
    have ha : s - (1 - conj ((actualCharacterZeros χ).zeros i)) =
        -conj (1 - conj s - (actualCharacterZeros χ).zeros i) := by simp; ring
    rw [ha, inv_neg, Complex.neg_re, neg_neg, ← map_inv₀, Complex.conj_re]
  have hsum := character_real_zero_summable χ s hs hs2
  constructor
  · simpa only [he, Function.comp_def] using
      (hsum.comp_injective (characterZeroIndexSelfReflection χ).injective).neg
  · unfold characterRealZeroSum
    simp_rw [he]
    rw [tsum_neg]
    congr 1
    exact (characterZeroIndexSelfReflection χ).tsum_eq
      (fun i => ((s - (actualCharacterZeros χ).zeros i)⁻¹).re)

/-- The conjugate functional equation cancels the constant term, yielding the
actual zero sum used in the full-height zero-free argument. -/
theorem complex_character_hadamard_identity (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    characterRealZeroSum χ s = (logDeriv χ.completed s).re +
      (1 / 2) * Real.log χ.modulus := by
  have hp := character_completed_partial_real_limit χ s (character_real_zero_summable χ s hs hs2)
  obtain ⟨hn, heq⟩ := character_real_zero_self_reflection χ s hs hs2
  have hm := character_completed_partial_real_limit χ (1 - conj s) hn
  have hc := completed_partial_fraction_difference_tendsto χ (1 - conj s) s
    (χ.completed_ne_zero_left _ (by simp; linarith)) (χ.completed_ne_zero_right _ hs.le)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  have hlim : characterRealZeroSum χ s - characterRealZeroSum χ (1 - conj s) =
      (logDeriv χ.completed s - logDeriv χ.completed (1 - conj s)).re := by
    apply tendsto_nhds_unique (hp.sub hm)
    simpa only [Function.comp_def, Complex.sub_re] using hr
  rw [heq, χ.completed_logDeriv_self_reflection s hs.le] at hlim
  simp only [Complex.sub_re, Complex.neg_re, Complex.conj_re, Complex.log_re, Complex.norm_natCast] at hlim
  linarith

end Ostmann

end OAI
