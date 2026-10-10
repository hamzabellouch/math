import Mathlib
import OAI.Probability.LogConcave.Analysis.Law

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

lemma Coupling.DistanceCoupled.integral_lipschitz {E : Type*}
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E} {R L C : ℝ}
    (h : Coupling.DistanceCoupled μ ν R) (hL : 0≤L) {f : E → ℝ}
    (hf : Measurable f) (hb : ∀x,|f x|≤C)
    (hl : ∀x y,|f x-f y|≤L*dist x y) :
    |(∫x,f x ∂μ)-(∫x,f x ∂ν)|≤L*R := by
  obtain ⟨κ,hκ,hx,hy,hd⟩ := h
  let := hκ
  have hix := bounded_integrable (hf.comp measurable_fst) (fun p : E×E => hb p.1) (μ:=κ)
  have hiy := bounded_integrable (hf.comp measurable_snd) (fun p : E×E => hb p.2) (μ:=κ)
  simp only [Function.comp_def] at hix hiy
  rw [←hx,←hy]
  change |(∫x,f x ∂κ.map Prod.fst)-(∫x,f x ∂κ.map Prod.snd)|≤_
  rw [integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,←integral_sub hix hiy,
    ←Real.norm_eq_abs]
  exact (norm_integral_le_of_norm_le_const (hd.mono (fun p hp =>
    (show ‖f p.1-f p.2‖≤L*dist p.1 p.2 by simpa only [Real.norm_eq_abs] using hl p.1 p.2).trans
      (mul_le_mul_of_nonneg_left hp hL)))).trans (by simp)

lemma TVAtMost.integral_unit {E : Type*} [MeasurableSpace E]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : TVAtMost μ ν ε) {f : E → ℝ} (hf : Measurable f)
    (hb : ∀x,0≤f x ∧ f x≤1) : |(∫x,f x ∂μ)-(∫x,f x ∂ν)|≤ε := by
  have hbf (x) : |f x|≤1 := by rw [abs_of_nonneg (hb x).1]; exact (hb x).2
  have hiμ := bounded_integrable hf hbf (μ:=μ)
  have hiν := bounded_integrable hf hbf (μ:=ν)
  have hlayer (ρ : Measure E) [IsProbabilityMeasure ρ] :
      Integrable (fun t : ℝ => ρ.real {x | t≤f x}) (volume.restrict (Set.Ioc 0 1)) := by
    apply bounded_integrable (C:=1)
    · exact (Antitone.measurable (show Antitone (fun t : ℝ => ρ {x | t≤f x}) from
        fun a b hab => measure_mono (fun x hx => hab.trans hx))).ennreal_toReal
    · intro t
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  rw [hiμ.integral_eq_integral_Ioc_meas_le (Filter.Eventually.of_forall (fun x => (hb x).1))
    (Filter.Eventually.of_forall (fun x => (hb x).2)),
    hiν.integral_eq_integral_Ioc_meas_le (Filter.Eventually.of_forall (fun x => (hb x).1))
    (Filter.Eventually.of_forall (fun x => (hb x).2)),←integral_sub (hlayer μ) (hlayer ν),←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (Set.Ioc (0:ℝ) 1))
    (f:=fun t : ℝ => μ.real {x | t≤f x}-ν.real {x | t≤f x}) (C:=ε)
    (Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using h {x | t≤f x} (measurableSet_le measurable_const hf)))
  simpa using hh

lemma kernel_integral_comp {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (κ : Kernel E F) [IsMarkovKernel κ]
    {f : F → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀x,|f x|≤C) :
    (∫z,f z ∂κ ∘ₘ μ)=∫x,(∫z,f z ∂κ x) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply]
  exact Kernel.integral_comp (bounded_integrable hf hb)

lemma kernel_event_real {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (κ : Kernel E F) [IsMarkovKernel κ]
    {s : Set F} (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s=∫x,(κ x).real s ∂μ := by
  rw [measureReal_def,Measure.bind_apply hs κ.aemeasurable]
  exact (integral_toReal (κ.measurable_coe hs).aemeasurable
    (Filter.Eventually.of_forall (fun x => measure_lt_top _ _))).symm

lemma kernel_event_integrable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (κ : Kernel E F) [IsMarkovKernel κ]
    {s : Set F} (hs : MeasurableSet s) : Integrable (fun x => (κ x).real s) μ :=
  bounded_integrable ((κ.measurable_coe hs).ennreal_toReal)
    (fun x => by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)

lemma TVAtMost.kernel {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : TVAtMost μ ν ε) (κ : Kernel E F) [IsMarkovKernel κ] :
    TVAtMost (κ ∘ₘ μ) (κ ∘ₘ ν) ε := by
  intro s hs
  rw [kernel_event_real μ κ hs,kernel_event_real ν κ hs]
  exact h.integral_unit ((κ.measurable_coe hs).ennreal_toReal)
    (fun x => ⟨measureReal_nonneg,measureReal_le_one⟩)

lemma TVAtMost.kernel_mixture {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (κ η : Kernel E F)
    [IsMarkovKernel κ] [IsMarkovKernel η] {e : E → ℝ}
    (hi : Integrable e μ) (h : ∀x,TVAtMost (κ x) (η x) (e x)) :
    TVAtMost (κ ∘ₘ μ) (η ∘ₘ μ) (∫x,e x ∂μ) := by
  intro s hs
  rw [kernel_event_real μ κ hs,kernel_event_real μ η hs,
    ←integral_sub (kernel_event_integrable μ κ hs) (kernel_event_integrable μ η hs),←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono ((kernel_event_integrable μ κ hs).sub (kernel_event_integrable μ η hs)).norm hi
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using h x s hs

end LogConcaveSampling

end

end

end OAI
