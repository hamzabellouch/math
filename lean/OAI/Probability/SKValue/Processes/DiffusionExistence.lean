import Mathlib
import OAI.Probability.SKValue.Processes.EulerLimitProcess

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter Function
open scoped Topology NNReal
namespace SKValue
noncomputable def terminalEulerProcess (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω):ℝ :=
  limsup (fun n:ℕ ↦ eulerLimitProcess W γ (terminalTime n) z) atTop
noncomputable def diffusionProcess (W:BrownianSpace) (γ:OrderParameter) (t:ℝ) (z:W.Ω):ℝ :=
  if t<1 then eulerLimitProcess W γ t z else terminalEulerProcess W γ z
lemma terminalEulerProcess_measurable (W:BrownianSpace) (γ:OrderParameter):
    StronglyMeasurable[W.filtration 1] (terminalEulerProcess W γ) :=by
  apply Measurable.stronglyMeasurable
  apply Measurable.limsup
  intro n
  apply ((eulerLimitProcess_measurable W γ (terminalTime n)).mono ?_).measurable
  apply W.filtration.mono
  exact Real.toNNReal_le_iff_le_coe.mpr (terminalTime_mem n).2.le
lemma diffusionProcess_measurable (W:BrownianSpace) (γ:OrderParameter) {t:ℝ}:
    StronglyMeasurable[W.filtration t.toNNReal] (diffusionProcess W γ t) :=by
  change StronglyMeasurable[W.filtration t.toNNReal] (fun z ↦ if t<1 then eulerLimitProcess W γ t z else terminalEulerProcess W γ z)
  by_cases ht:t<1
  · simp only [ite_eq_left ht]
    exact eulerLimitProcess_measurable W γ t
  · simp only [ite_eq_right ht]
    apply (terminalEulerProcess_measurable W γ).mono (W.filtration.mono ?_)
    exact (Real.le_toNNReal_iff_coe_le (zero_le_one.trans (not_lt.mp ht))).mpr (not_lt.mp ht)
lemma diffusionProcess_adapted (W:BrownianSpace) (γ:OrderParameter):
    Adapted W.filtration (fun t z ↦ diffusionProcess W γ (min (t:ℝ) 1) z) :=by
  intro t
  apply ((diffusionProcess_measurable W γ (t:=min (t:ℝ) 1)).mono ?_).measurable
  apply W.filtration.mono
  exact Real.toNNReal_le_iff_le_coe.mpr (min_le_left _ _)
lemma diffusionProcess_path (W:BrownianSpace) (γ:OrderParameter) (z:W.Ω)
    (hb:Continuous (fun t:ℝ ↦ W.B t.toNNReal z)) (h0:W.B 0 z=0):
    ContinuousOn (fun t ↦ diffusionProcess W γ t z) (Icc (0:ℝ) 1) ∧
    ∀t∈Icc (0:ℝ) 1,diffusionProcess W γ t z=W.B t.toNNReal z+
      ∫s in (0:ℝ)..t,γ.coeff s*gradient W γ s (diffusionProcess W γ s z) :=by
  let f:=fun s ↦ γ.coeff s*gradient W γ s (eulerLimitProcess W γ s z)
  let F:=fun t ↦ W.B t.toNNReal z+∫s in (0:ℝ)..t,f s
  have hi:IntervalIntegrable f volume 0 1:=eulerLimitProcess_drift_integrable W γ z hb h0
  have hc:ContinuousOn F (Icc (0:ℝ) 1):=by
    apply hb.continuousOn.add
    simpa only [uIcc_of_le (by norm_num:(0:ℝ)≤1)] using
      intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have he:∀t∈Ico (0:ℝ) 1,eulerLimitProcess W γ t z=F t:=by
    intro t ht
    exact (eulerLimitProcess_local_path W γ z hb h0 ht).2.2 t ⟨ht.1,le_rfl⟩
  have hl:Tendsto (fun n ↦ eulerLimitProcess W γ (terminalTime n) z) atTop (𝓝 (F 1)):=by
    have htime:Tendsto terminalTime atTop (𝓝[Icc (0:ℝ) 1] (1:ℝ)):=
      tendsto_nhdsWithin_iff.mpr ⟨(tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1,
        Eventually.of_forall (fun n ↦ ⟨(terminalTime_mem n).1,(terminalTime_mem n).2.le⟩)⟩
    apply ((hc 1 ⟨by norm_num,le_rfl⟩).tendsto.comp htime).congr
    intro n
    exact (he _ (terminalTime_mem n)).symm
  have hU:terminalEulerProcess W γ z=F 1:=hl.limsup_eq
  have hEq (t:ℝ) (ht:t∈Icc (0:ℝ) 1):diffusionProcess W γ t z=F t:=by
    by_cases ht1:t<1
    · simpa only [diffusionProcess,ite_eq_left ht1] using he t ⟨ht.1,ht1⟩
    · have ht':t=1:=le_antisymm ht.2 (not_lt.mp ht1)
      subst t
      simpa only [diffusionProcess,lt_self_iff_false,ite_false] using hU
  refine ⟨hc.congr hEq,?_⟩
  intro t ht
  rw [hEq t ht]
  change W.B t.toNNReal z+(∫s in (0:ℝ)..t,f s)=_
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le ht.1
  intro s hs
  simp only [f,diffusionProcess,ite_eq_left (hs.2.trans_le ht.2)]
theorem diffusionProcess_isDiffusion (W:BrownianSpace) (γ:OrderParameter):IsDiffusion W γ (diffusionProcess W γ) :=by
  refine ⟨diffusionProcess_adapted W γ,?_⟩
  filter_upwards [W.brownian.cont,W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero] with z hz h0
  exact diffusionProcess_path W γ z (hz.comp (by fun_prop:Continuous (fun t:ℝ ↦ t.toNNReal))) h0
lemma exists_diffusion (W:BrownianSpace) (γ:OrderParameter):∃X:ℝ → W.Ω → ℝ,IsDiffusion W γ X:=
  ⟨diffusionProcess W γ,diffusionProcess_isDiffusion W γ⟩
end SKValue

end

end OAI
