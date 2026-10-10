import OAI.Probability.PosteriorReplicas.Information.FiniteEntropyBounds

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma atom_smul_kernel_le_snd {V X : Type*} [MeasurableSpace V] [MeasurableSpace X]
    [MeasurableSingletonClass V] (μ : Measure V) [IsProbabilityMeasure μ]
    (κ : Kernel V X) [IsMarkovKernel κ] (v : V) :
    μ {v} • κ v ≤ (μ ⊗ₘ κ).snd := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.smul_apply,smul_eq_mul,Measure.snd_compProd,
    Measure.bind_apply hs κ.measurable.aemeasurable]
  calc
    _ = ∫⁻ w in {v}, κ w s ∂μ := by rw [lintegral_singleton,mul_comm]
    _ ≤ ∫⁻ w, κ w s ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl

lemma finite_state_bounded_density {V X : Type*} [MeasurableSpace V] [MeasurableSpace X]
    [MeasurableSingletonClass V] (μ : Measure V) [IsProbabilityMeasure μ]
    (κ : Kernel V X) [IsMarkovKernel κ] (ν : Measure X) [IsProbabilityMeasure ν]
    (hν : (μ ⊗ₘ κ).snd = ν) (v : V) (hv : μ {v} ≠ 0) :
    ∃ f : X → ℝ≥0∞, Measurable f ∧ (∀ x, f x ≤ ENNReal.ofReal ((μ.real {v})⁻¹)) ∧
      ν.withDensity f = κ v := by
  let τ := μ {v} • κ v
  have hle : τ ≤ ν := hν ▸ atom_smul_kernel_le_snd μ κ v
  have : IsFiniteMeasure τ := isFiniteMeasure_of_le ν hle
  let g : X → ℝ≥0∞ := fun x => min (τ.rnDeriv ν x) 1
  have hg : Measurable g := (Measure.measurable_rnDeriv τ ν).min measurable_const
  have he : ν.withDensity g = τ := by
    rw [withDensity_congr_ae (show g =ᵐ[ν] τ.rnDeriv ν by
      filter_upwards [Measure.rnDeriv_le_one_of_le hle] with x hx
      exact min_eq_left hx)]
    exact Measure.withDensity_rnDeriv_eq τ ν (Measure.absolutelyContinuous_of_le hle)
  refine ⟨fun x => (μ {v})⁻¹*g x,measurable_const.mul hg,?_,?_⟩
  · intro x
    have ha : 0 < μ.real {v} := ENNReal.toReal_pos hv (measure_ne_top μ {v})
    rw [ENNReal.ofReal_inv_of_pos ha,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ {v})]
    calc
      _ ≤ (μ {v})⁻¹*1 := mul_le_mul le_rfl (min_le_right _ _) (by positivity) (by positivity)
      _ = _ := mul_one _
  · change ν.withDensity ((μ {v})⁻¹ • g) = κ v
    rw [withDensity_smul _ hg,he]
    change (μ {v})⁻¹ • (μ {v} • κ v) = _
    rw [smul_smul,ENNReal.inv_mul_cancel hv (measure_ne_top μ {v}),one_smul]

end PosteriorReplicas
end

end OAI
