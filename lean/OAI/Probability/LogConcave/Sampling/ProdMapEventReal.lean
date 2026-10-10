import Mathlib
import OAI.Probability.LogConcave.Complexity.KernelAnalyticNormalizedBudget
import OAI.Probability.LogConcave.Dynamics.Squared
import OAI.Probability.LogConcave.Analysis.AffinePotential

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped NNReal

lemma prod_map_event_real {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace E] (μ : Measure Ω) (ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × G → E) (hf : Measurable f) {A : Set E} (hA : MeasurableSet A) :
    ((μ.prod ν).map f).real A = ∫x,ν.real ((fun z => f (x,z)) ⁻¹' A) ∂μ := by
  rw [measureReal_def,Measure.map_apply hf hA,Measure.prod_apply (hA.preimage hf)]
  exact (integral_toReal (measurable_measure_prodMk_left (hA.preimage hf)).aemeasurable
    (Filter.Eventually.of_forall (fun _ => measure_lt_top _ _))).symm

lemma prod_event_integrable {Ω G E : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSpace E] (μ : Measure Ω) (ν : Measure G)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω × G → E) (hf : Measurable f) {A : Set E} (hA : MeasurableSet A) :
    Integrable (fun x => ν.real ((fun z => f (x,z)) ⁻¹' A)) μ := by
  have hm : Measurable (fun x => ν.real ((fun z => f (x,z)) ⁻¹' A)) :=
    (measurable_measure_prodMk_left (hA.preimage hf)).ennreal_toReal
  apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one)

theorem TVAtMost_gaussian_mixture {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (f g : Ω → Point d) (hf : Measurable f) (hg : Measurable g)
    {s : ℝ} (hs : 0<s) (hi : Integrable (fun z => ‖f z-g z‖) μ) :
    TVAtMost ((μ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2))
      ((μ.prod (stdGaussian (Point d))).map (fun z => g z.1+s • z.2))
      ((∫z,‖f z-g z‖ ∂μ)/s) := by
  intro A hA
  have hf' : Measurable (fun z : Ω × Point d => f z.1+s • z.2) := by fun_prop
  have hg' : Measurable (fun z : Ω × Point d => g z.1+s • z.2) := by fun_prop
  rw [prod_map_event_real μ _ _ hf' hA,prod_map_event_real μ _ _ hg' hA,
    ←integral_sub (prod_event_integrable μ _ _ hf' hA) (prod_event_integrable μ _ _ hg' hA)]
  rw [←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [←integral_div]
  apply integral_mono ((prod_event_integrable μ _ _ hf' hA).sub
    (prod_event_integrable μ _ _ hg' hA)).norm (hi.div_const s)
  intro z
  have hh := TVAtMost_gaussian_affine (f z) (g z) hs A hA
  rw [measureReal_def,measureReal_def,
    Measure.map_apply (show Measurable (fun u : Point d => f z+s • u) by fun_prop) hA,
    Measure.map_apply (show Measurable (fun u : Point d => g z+s • u) by fun_prop) hA] at hh
  simpa only [Real.norm_eq_abs,Pi.sub_apply,measureReal_def] using hh

namespace Coupling
variable {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {d : ℕ}

theorem SquaredAt.gaussian_smoothing {μ : Measure Ω} {ν : Measure Γ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → Point d} {g : Γ → Point d} (hf : Measurable f) (hg : Measurable g)
    {B s : ℝ} (hs : 0<s) (hc : SquaredAt μ ν f g B) :
    TVAtMost ((μ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2))
      ((ν.prod (stdGaussian (Point d))).map (fun z => g z.1+s • z.2)) (Real.sqrt B/s) := by
  obtain ⟨κ,hκ,hl,hr,hi,he⟩ := hc
  let := hκ
  have hm : Measurable (fun z : Ω × Γ => ‖f z.1-g z.2‖) := by fun_prop
  have h2 := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi
  have h1 := h2.integrable (by norm_num : (1:ENNReal)≤2)
  have hcs := integral_mul_sq_le h2 (memLp_const (1:ℝ) (μ:=κ))
  simp only [mul_one,one_pow,integral_const,probReal_univ,smul_eq_mul] at hcs
  have hB : 0≤B := (integral_nonneg (fun z => sq_nonneg ‖f z.1-g z.2‖)).trans he
  have hsmall : (∫z : Ω × Γ,‖f z.1-g z.2‖ ∂κ)≤Real.sqrt B :=
    (Real.le_sqrt (integral_nonneg (fun _ => norm_nonneg _)) hB).2 (hcs.trans he)
  have htv := (TVAtMost_gaussian_mixture κ (fun z => f z.1) (fun z => g z.2)
    (hf.comp measurable_fst) (hg.comp measurable_snd) hs h1).mono
      (div_le_div_of_nonneg_right hsmall hs.le)
  have mapLeft : (κ.prod (stdGaussian (Point d))).map (fun z => f z.1.1+s • z.2)=
      (μ.prod (stdGaussian (Point d))).map (fun z => f z.1+s • z.2) := by
    have hp : (κ.prod (stdGaussian (Point d))).map (Prod.map Prod.fst id)=μ.prod (stdGaussian (Point d)) := by
      rw [←Measure.map_prod_map _ _ measurable_fst measurable_id,Measure.map_id]
      exact congrArg (fun m => m.prod (stdGaussian (Point d))) hl
    rw [←hp,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have mapRight : (κ.prod (stdGaussian (Point d))).map (fun z => g z.1.2+s • z.2)=
      (ν.prod (stdGaussian (Point d))).map (fun z => g z.1+s • z.2) := by
    have hp : (κ.prod (stdGaussian (Point d))).map (Prod.map Prod.snd id)=ν.prod (stdGaussian (Point d)) := by
      rw [←Measure.map_prod_map _ _ measurable_snd measurable_id,Measure.map_id]
      exact congrArg (fun m => m.prod (stdGaussian (Point d))) hr
    rw [←hp,Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rwa [mapLeft,mapRight] at htv
end Coupling
end LogConcaveSampling

end

end

end OAI
