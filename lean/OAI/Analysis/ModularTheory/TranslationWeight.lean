import OAI.Analysis.ModularTheory.TranslationCalculus
import OAI.Analysis.OperatorAlgebra.LpFourierCoefficients
import OAI.Analysis.ModularTheory.CoreSquareWeight

namespace OAI

/-! The regular translation calculus acts on the scalar weight vectors by
ordinary frequency multiplication. Integrable frequency envelopes therefore
give actual finite-weight elements of the core. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped ENNReal

namespace WeakPureInfiniteness

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma vectorLpRepresentation_compLp (L : H →L[ℂ] K)
    (g : BoundedContinuousFunction ℝ ℂ) (f : Lp H 2 (volume : Measure ℝ)) :
    vectorLpRepresentation volume g (L.compLpL 2 volume f) =
      L.compLpL 2 volume (vectorLpRepresentation volume g f) := by
  apply Lp.ext
  filter_upwards [vectorLpMultiplier_ae volume g (L.compLpL 2 volume f),
    L.coeFn_compLpL f, L.coeFn_compLpL (vectorLpRepresentation volume g f),
    vectorLpMultiplier_ae volume g f] with t h₁ h₂ h₃ h₄
  change (vectorLpMultiplier volume g (L.compLpL 2 volume f)) t =
    (L.compLpL 2 volume (vectorLpRepresentation volume g f)) t
  change (vectorLpRepresentation volume g f) t = g t • f t at h₄
  rw [h₁, h₂, h₃, h₄, map_smul]

lemma vectorLpRepresentation_complex (g : BoundedContinuousFunction ℝ ℂ) :
    vectorLpRepresentation (H := ℂ) (volume : Measure ℝ) g =
      scalarLpRepresentation volume g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [vectorLpMultiplier_ae volume g f, scalarLpMultiplier_ae volume g f]
    with t h₁ h₂
  exact h₁.trans h₂.symm

variable (S : BoundedRecovery.StandardModularData H)

lemma modularTranslationCalculus_fourierInclusion
    (g : BoundedContinuousFunction ℝ ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modularTranslationCalculus g (modularFourierInclusion S f) =
      modularFourierInclusion S (scalarLpRepresentation volume g f) := by
  change 𝓕⁻ (vectorLpRepresentation volume g
    (𝓕 ((ContinuousLinearMap.toSpanSingleton ℂ S.xi).compLpL 2 volume (𝓕⁻ f)))) =
    (ContinuousLinearMap.toSpanSingleton ℂ S.xi).compLpL 2 volume
      (𝓕⁻ (scalarLpRepresentation volume g f))
  rw [fourier_compLp, fourier_fourierInv_eq, vectorLpRepresentation_compLp,
    vectorLpRepresentation_complex, fourierInv_compLp]

lemma modularTranslationCalculus_weightNorm
    (g : BoundedContinuousFunction ℝ ℂ) (n : ℕ) :
    ‖modularTranslationCalculus g (modularCoreWeightVector S n)‖ =
      ‖scalarLpRepresentation volume g (modularWeightCutoffVector n)‖ := by
  rw [modularCoreWeightVector, modularTranslationCalculus_fourierInclusion,
    (modularFourierInclusion S).norm_map]

lemma modularTranslationCalculus_weight_le
    (g : BoundedContinuousFunction ℝ ℂ)
    (hi : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t))) :
    modularCoreSquareWeight S (modularTranslationCalculus g) ≤
      ENNReal.ofReal (∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (2 * Real.pi * t)) := by
  apply iSup_le
  intro n
  apply ENNReal.ofReal_le_ofReal
  rw [modularTranslationCalculus_weightNorm, scalarLp_norm_sq_integral]
  have hi' := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (scalarLpRepresentation volume g
      (modularWeightCutoffVector n)))).mp (Lp.memLp _)
  apply integral_mono_ae hi' hi
  filter_upwards [scalarLpMultiplier_ae volume g (modularWeightCutoffVector n),
    modularWeightCutoffVector_ae n] with t h₁ h₂
  change ‖scalarLpMultiplier volume g (modularWeightCutoffVector n) t‖ ^ 2 ≤ _
  rw [h₁, h₂]
  by_cases ht : t ∈ Set.Icc (-(n : ℝ)) n
  · rw [modularWeightCutoffFunction, Set.indicator_of_mem ht, norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (Real.pi * t) ^ 2 = Real.exp (2 * Real.pi * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num; ring
    rw [he]
  · rw [modularWeightCutoffFunction, Set.indicator_of_notMem ht, mul_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

end WeakPureInfiniteness

end

end OAI
