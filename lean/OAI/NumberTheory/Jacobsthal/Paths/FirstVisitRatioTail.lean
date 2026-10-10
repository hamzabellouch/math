import OAI.NumberTheory.Jacobsthal.Estimates.EvenInverseBands

namespace OAI

namespace Erdos970


open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
namespace ErdosHighRatioBandTail
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.KernelDensityBridge NumberTheoryLean.CompactExponentialMoments

theorem costKernel_highStates (s : State) (c T : ℝ) :
    costKernel (s,c) (Prod.fst ⁻¹' highStates T) = stateKernel s (highStates T) := by
  rw [costKernel_apply _ (measurable_fst (highStates_measurable T))]
  rfl

theorem even_state_high (s : EvenState) (T : ℝ) :
    stateKernel (.inl s) (highStates T) = evenKernel s (Ici T) := by
  rw [← stateKernel_even_ratio s, Measure.map_apply stateRatio_measurable measurableSet_Ici]
  rfl

theorem first_band_tail_bound : ∃ U : ℝ, 4 ≤ U ∧
    ∀ T : ℝ, U ≤ T → ∀ v h : ℝ, ∀ s : EvenState, s.1 ≤ 23/10 →
      costKernel (.inl s,0) (highBand T v h) ≤
        ENNReal.ofReal (Real.exp (-2*(T-(U-1)))) := by
  obtain ⟨U,hU,he,_ho⟩ := kernel_uniform_upper_tails
  refine ⟨U,hU,?_⟩
  intro T hT v h s hs
  have ht := he U le_rfl s (by linarith) (T-(U-1)) (by linarith)
  rw [show U-1+(T-(U-1))=T by ring] at ht
  calc
    _ ≤ costKernel (.inl s,0) (Prod.fst ⁻¹' highStates T) :=
      measure_mono (fun _ hz => hz.1)
    _ = evenKernel s (Ici T) := by rw [costKernel_highStates, even_state_high]
    _ ≤ _ := ht

theorem exponential_tail_tendsto (U : ℝ) :
    Tendsto (fun T : ℝ => ENNReal.ofReal (Real.exp (-2*(T-(U-1))))) atTop (𝓝 0) := by
  have hsub : Tendsto (fun T : ℝ => T-(U-1)) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      tendsto_atTop_add_const_right atTop (-(U-1)) (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hlin : Tendsto (fun T : ℝ => 2*(T-(U-1))) atTop atTop :=
    hsub.const_mul_atTop (by norm_num)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hh := (ENNReal.continuous_ofReal.tendsto 0).comp he
  simpa only [Function.comp_def, neg_mul, ENNReal.ofReal_zero] using hh

end ErdosHighRatioBandTail


end Erdos970

end OAI
