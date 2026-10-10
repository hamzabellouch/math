import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter

namespace Problem367

theorem integral_of_conditional_versions
    {T Ω : Type*} [mT : MeasurableSpace T] (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (ν : Measure T) (μ : Measure Ω) [SFinite ν] [SFinite μ]
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {F G : T × Ω → ℝ}
    (hF : Integrable F (ν.prod μ)) (hG : Integrable G (ν.prod μ))
    (hGm : StronglyMeasurable[@MeasurableSpace.prod T Ω mT m] G)
    (hcond : ∀ᵐ t ∂ν,
      (fun ω => G (t, ω)) =ᵐ[μ] μ[(fun ω => F (t, ω)) | m]) :
    (fun ω => ∫ t, G (t, ω) ∂ν) =ᵐ[μ]
      μ[(fun ω => ∫ t, F (t, ω) ∂ν) | m] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hF.integral_prod_right
  · intro s hs hfin
    exact hG.integral_prod_right.integrableOn
  · intro s hs hfin
    have hFrestrict : Integrable F (ν.prod (μ.restrict s)) :=
      hF.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hGrestrict : Integrable G (ν.prod (μ.restrict s)) :=
      hG.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    calc
      (∫ ω in s, ∫ t, G (t, ω) ∂ν ∂μ) =
          ∫ t, ∫ ω in s, G (t, ω) ∂μ ∂ν :=
        (integral_integral_swap (f := fun t ω => G (t, ω)) hGrestrict).symm
      _ = ∫ t, ∫ ω in s, F (t, ω) ∂μ ∂ν := by
        apply integral_congr_ae
        filter_upwards [hcond, hF.prod_right_ae] with t ht hFt
        exact (setIntegral_congr_ae (hm s hs) (ht.mono (fun ω hω _ => hω))).trans
          (setIntegral_condExp hm hFt hs)
      _ = ∫ ω in s, ∫ t, F (t, ω) ∂ν ∂μ :=
        integral_integral_swap (f := fun t ω => F (t, ω)) hFrestrict
  · have hgm : StronglyMeasurable[m] (fun ω => ∫ t, G (t, ω) ∂ν) := by
      let : MeasurableSpace Ω := m
      exact hGm.integral_prod_left'
    exact hgm.aestronglyMeasurable

theorem condExp_setIntegral_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ mΩ) {f : ℝ → Ω → ℝ} (hf : Martingale f ℱ μ)
    {s t : ℝ} (hst : s ≤ t)
    (hInt : Integrable (fun p : ℝ × Ω => f p.1 p.2)
      ((volume.restrict (Set.Ioc s t)).prod μ)) :
    μ[(fun ω => ∫ u in Set.Ioc s t, f u ω) | ℱ s] =ᵐ[μ]
      (fun ω => (t - s) * f s ω) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc s t)
  have hGm : StronglyMeasurable[@MeasurableSpace.prod ℝ Ω inferInstance (ℱ s)]
      (fun p : ℝ × Ω => f s p.2) := by
    let : MeasurableSpace Ω := ℱ s
    exact (hf.stronglyMeasurable s).comp_measurable measurable_snd
  have hcond : ∀ᵐ u ∂ν,
      (fun ω => f s ω) =ᵐ[μ] μ[(fun ω => f u ω) | ℱ s] := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (hf.condExp_ae_eq hu.1.le).symm
  have h := integral_of_conditional_versions (ℱ s) ν μ (ℱ.le s)
    hInt ((hf.integrable s).comp_snd ν) hGm hcond
  simpa [ν, Real.volume_real_Ioc_of_le hst] using h.symm

theorem condExp_intervalIntegral_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℝ mΩ) {f : ℝ → Ω → ℝ} (hf : Martingale f ℱ μ)
    {s t : ℝ} (hst : s ≤ t)
    (hInt : Integrable (fun p : ℝ × Ω => f p.1 p.2)
      ((volume.restrict (Set.Ioc s t)).prod μ)) :
    μ[(fun ω => ∫ u in s..t, f u ω) | ℱ s] =ᵐ[μ]
      (fun ω => (t - s) * f s ω) := by
  simpa only [intervalIntegral.integral_of_le hst] using
    condExp_setIntegral_martingale μ ℱ hf hst hInt

end Problem367

end

end OAI
