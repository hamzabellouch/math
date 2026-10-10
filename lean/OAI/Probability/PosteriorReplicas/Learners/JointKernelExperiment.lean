import OAI.Probability.PosteriorReplicas.Learners.KernelSuccess

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression

namespace JointKernelExperiment
open Learner

instance law_probability {d M T : ℕ} [NeZero d] {Ω : Type u} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] (E : JointKernelExperiment d M T Ω ρ) :
    IsProbabilityMeasure E.law := by
  unfold law
  infer_instance

lemma uniformSuccess_eq_average {d M T : ℕ} [NeZero d] {Ω : Type u} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] (E : JointKernelExperiment d M T Ω ρ) (ε : ℝ) :
    E.uniformSuccess ε = ∫⁻ ω, (E.rules ω).uniformSuccess T ε ∂ρ := by
  have hS : MeasurableSet {z : (Ω × (UnitSphere d × Samples d T)) × UnitSphere d |
      angularError z.1.2.1 z.2 ≤ ε} := by
    exact measurableSet_le (Real.continuous_arccos.measurable.comp
      ((measurable_subtype_coe.comp measurable_snd).inner
        (measurable_subtype_coe.comp measurable_fst.snd.fst))) measurable_const
  have hm := Kernel.measurable_kernel_prodMk_left (κ := E.outputKernel) hS
  rw [uniformSuccess,law,Measure.compProd_apply hS,lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [E.conditional_output] with ω hω
  apply lintegral_congr_ae
  filter_upwards [hω] with z hz
  rw [hz]
  rfl

lemma exists_seed_ge_success {d M T : ℕ} [NeZero d] {Ω : Type u} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] (E : JointKernelExperiment d M T Ω ρ) (ε : ℝ) :
    ∃ ω, E.uniformSuccess ε ≤ (E.rules ω).uniformSuccess T ε := by
  rw [E.uniformSuccess_eq_average ε]
  apply exists_lintegral_le
  apply ne_of_lt
  apply lt_of_le_of_lt (lintegral_mono (fun ω => (E.rules ω).uniformSuccess_le_one T ε))
  simp

lemma fixed_quadratic_memory {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    {ρ : Measure Ω} [IsProbabilityMeasure ρ] {A : ℝ} (hA : 0<A) (hd : 32≤d)
    (hM : (M : ℝ)≤A*(d : ℝ)^2) {ε : ℝ} (hε : 0<ε) (hε10 : ε≤1/10)
    (E : JointKernelExperiment d M T Ω ρ) (hs : (2/3 : ℝ≥0∞) ≤ E.uniformSuccess ε) :
    (1/(4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨ω,hω⟩ := E.exists_seed_ge_success ε
  exact (E.rules ω).fixed_quadratic_memory hA hd hM hε hε10 (hs.trans hω)

end JointKernelExperiment

theorem kernel_subquadratic_memory : KernelSubquadraticMemory.{u} := by
  refine ⟨1/(4*(400000+100*(1:ℝ))),by positivity,?_⟩
  intro M hM
  obtain ⟨d₂, hd₂⟩ := eventually_atTop.1 hM.eventuallyLE
  refine ⟨max 32 d₂, ?_⟩
  intro d hd T ε hε hε10 Ω _ ρ hρ E hs
  have : IsProbabilityMeasure ρ := hρ
  have hmem : (M d : ℝ) ≤ 1 * (d : ℝ)^2 := by
    have hm := hd₂ d (by omega)
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (M d) : (0:ℝ)≤M d),
      abs_of_nonneg (sq_nonneg (d : ℝ)),one_mul] using hm
  exact E.fixed_quadratic_memory (by norm_num) (by omega) hmem hε hε10 hs

end PosteriorRegression
end

end OAI
