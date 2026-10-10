import OAI.Probability.PosteriorReplicas.Information.ConditionalKL

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section Finite
variable {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]

omit [MeasurableSingletonClass W] in
lemma finite_ac_of_singleton {μ ν : Measure W}
    (h : ∀ w, ν {w} = 0 → μ {w} = 0) : μ ≪ ν := by
  intro s hs
  apply measure_eq_zero_iff_ae_notMem.mpr
  apply ae_iff_of_countable.mpr
  intro w hw hws
  exact hw (h w (measure_mono_null (singleton_subset_iff.mpr hws) hs))

lemma finite_withDensity_ratio (μ ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) : ν.withDensity (fun w => μ {w} / ν {w}) = μ := by
  apply Measure.ext_of_singleton
  intro w
  rw [withDensity_apply _ (measurableSet_singleton w), lintegral_singleton]
  by_cases h : ν {w} = 0
  · simp [h, hac h]
  · exact ENNReal.div_mul_cancel h (measure_ne_top ν {w})

lemma finite_llr_ratio (μ ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : μ ≪ ν) : llr μ ν =ᵐ[μ] (fun w => Real.log (μ.real {w} / ν.real {w})) := by
  have hd : μ.rnDeriv ν =ᵐ[ν] (fun w => μ {w} / ν {w}) := by
    conv_lhs => rw [← finite_withDensity_ratio μ ν hac]
    exact Measure.rnDeriv_withDensity _ (measurable_of_countable _)
  filter_upwards [hac.ae_le hd] with w hw
  simp only [llr, hw, ENNReal.toReal_div, measureReal_def]

lemma finite_klDiv_formula (μ ν : Measure W) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) :
    klDiv μ ν = ENNReal.ofReal (∑ w, μ.real {w} * Real.log (μ.real {w} / ν.real {w})) := by
  rw [klDiv_of_ac_of_integrable hac Integrable.of_finite]
  rw [integral_congr_ae (finite_llr_ratio μ ν hac), integral_fintype Integrable.of_finite]
  simp [smul_eq_mul, measureReal_def]

lemma finite_klDiv_le_crossEntropy (μ ν : Measure W)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    klDiv μ ν ≤ ENNReal.ofReal (∑ w, μ.real {w} * (-Real.log (ν.real {w}))) := by
  rw [finite_klDiv_formula μ ν hac]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : μ {w} = 0
  · simp [measureReal_def, hw]
  · have hw' : 0 < μ.real {w} := ENNReal.toReal_pos hw (measure_ne_top μ {w})
    have hv : ν {w} ≠ 0 := fun h => hw (hac h)
    have hv' : 0 < ν.real {w} := ENNReal.toReal_pos hv (measure_ne_top ν {w})
    rw [Real.log_div hw'.ne' hv'.ne']
    apply mul_le_mul_of_nonneg_left _ hw'.le
    have hl := Real.log_nonpos hw'.le (measureReal_le_one (μ := μ) (s := {w}))
    linarith

omit [MeasurableSingletonClass W] in
lemma finite_crossEntropy_nonneg (μ ν : Measure W)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ ∑ w, μ.real {w} * (-Real.log (ν.real {w})) := by
  apply Finset.sum_nonneg
  intro w _
  apply mul_nonneg measureReal_nonneg
  exact neg_nonneg.mpr (Real.log_nonpos measureReal_nonneg measureReal_le_one)

end Finite

section Kernel
variable {X W : Type*} [MeasurableSpace X] [Fintype W] [MeasurableSpace W]
  [MeasurableSingletonClass W]
  (μ : Measure X) [IsProbabilityMeasure μ] (κ : Kernel X W) [IsMarkovKernel κ]

lemma ae_kernel_ac_marginal : ∀ᵐ x ∂μ, κ x ≪ (μ ⊗ₘ κ).snd := by
  have h : ∀ w : W, ∀ᵐ x ∂μ, (μ ⊗ₘ κ).snd {w} = 0 → κ x {w} = 0 := by
    intro w
    by_cases hw : (μ ⊗ₘ κ).snd {w} = 0
    · have he : (∫⁻ x, κ x {w} ∂μ) = 0 := by
        rw [Measure.snd_compProd, Measure.bind_apply (measurableSet_singleton w) κ.measurable.aemeasurable] at hw
        exact hw
      filter_upwards [(lintegral_eq_zero_iff (Kernel.measurable_coe κ (measurableSet_singleton w))).mp he]
        with x hx
      exact fun _ => hx
    · exact ae_of_all _ (fun _ => fun h => (hw h).elim)
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact finite_ac_of_singleton hx

omit [Fintype W] in
lemma integrable_kernel_atom (w : W) : Integrable (fun x => (κ x).real {w}) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((Kernel.measurable_coe κ (measurableSet_singleton w)).ennreal_toReal.aestronglyMeasurable)
  exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, measureReal_def] using
    (measureReal_le_one (μ := κ x) (s := {w}))

omit [Fintype W] in
lemma integral_kernel_atom (w : W) :
    ∫ x, (κ x).real {w} ∂μ = (μ ⊗ₘ κ).snd.real {w} := by
  rw [measureReal_def, Measure.snd_compProd,
    Measure.bind_apply (measurableSet_singleton w) κ.measurable.aemeasurable]
  simp only [measureReal_def]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    ((Kernel.measurable_coe κ (measurableSet_singleton w)).ennreal_toReal.aestronglyMeasurable)]
  congr 1
  apply lintegral_congr
  intro x
  exact ENNReal.ofReal_toReal (measure_ne_top (κ x) {w})

lemma klDiv_kernel_le_finiteEntropy :
    klDiv (μ ⊗ₘ κ) (μ.prod (μ ⊗ₘ κ).snd) ≤
      ENNReal.ofReal (finiteEntropy (μ ⊗ₘ κ).snd) := by
  rw [← Measure.compProd_const, klDiv_compProd_kernel]
  let ν := (μ ⊗ₘ κ).snd
  have hi : Integrable (fun x => ∑ w : W, (κ x).real {w} * (-Real.log (ν.real {w}))) μ := by
    apply integrable_finsetSum
    intro w _
    exact (integrable_kernel_atom μ κ w).mul_const _
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (∑ w : W, (κ x).real {w} * (-Real.log (ν.real {w}))) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_kernel_ac_marginal μ κ] with x hx
      exact finite_klDiv_le_crossEntropy (κ x) ν hx
    _ = ENNReal.ofReal (∫ x, ∑ w : W, (κ x).real {w} * (-Real.log (ν.real {w})) ∂μ) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => finite_crossEntropy_nonneg (κ x) ν)
    _ = _ := by
      rw [integral_finsetSum _ (fun w _ => (integrable_kernel_atom μ κ w).mul_const _)]
      simp_rw [integral_mul_const, integral_kernel_atom μ κ]
      congr 1
      unfold finiteEntropy
      apply Finset.sum_congr rfl
      intro w _
      ring

end Kernel

lemma mutualInformation_le_finiteEntropy {X W : Type*} [MeasurableSpace X]
    [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    [StandardBorelSpace W] [Nonempty W]
    (q : Measure (X × W)) [IsProbabilityMeasure q] :
    klDiv q (q.fst.prod q.snd) ≤ ENNReal.ofReal (finiteEntropy q.snd) := by
  have h := klDiv_kernel_le_finiteEntropy q.fst q.condKernel
  simpa only [Measure.disintegrate q q.condKernel] using h

end PosteriorReplicas
end

end OAI
