import OAI.Analysis.LipschitzHilbert.Estimates.CompactMollificationFamily

namespace OAI

/-! Positive compact mollification converges in L2 for bounded compact
measurable tests, with a common compact support. -/
noncomputable section
open MeasureTheory Function Set Filter
open scoped Topology Convolution Pointwise
namespace LipschitzHilbert.PacketRepresentation

theorem compactMollification_energy_tendsto (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (hb : ∀ z, ‖f z‖≤1) :
    Tendsto (fun n => ∫ z, ‖compactMollification (testMollifier n) f hf hc z-f z‖^2 ∂planeMeasure)
      atTop (nhds 0) := by
  let S := Metric.closedBall (0 : ℝ×ℝ) 1+tsupport f
  have hS : IsCompact S := (isCompact_closedBall _ _).add hc
  have hfs : support f⊆S := by
    intro z hz
    exact Set.mem_add.mpr ⟨0,by simp,z,subset_closure hz,zero_add z⟩
  have hgs (n : ℕ) : support (compactMollification (testMollifier n) f hf hc)⊆S :=
    compactMollification_common_support f hf hc n
  have hdom : Integrable (S.indicator (fun _ => (4:ℝ))) planeMeasure :=
    (integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet
  have h := tendsto_integral_of_dominated_convergence (μ:=planeMeasure)
    (S.indicator (fun _ => (4:ℝ)))
    (F:=fun n z => ‖compactMollification (testMollifier n) f hf hc z-f z‖^2) (f:=fun _ => (0:ℝ))
    (fun n => (((compactMollification (testMollifier n) f hf hc).continuous.measurable.sub hfm).norm.pow_const 2).aestronglyMeasurable)
    hdom (fun n => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hz : z∈S
      · rw [Set.indicator_of_mem hz]
        have hn : ‖compactMollification (testMollifier n) f hf hc z-f z‖≤2 :=
          (norm_sub_le _ _).trans (by linarith only [compactMollification_unit (testMollifier n) f hf hc hb z,hb z])
        simpa only [show (2:ℝ)^2=4 by norm_num] using pow_le_pow_left₀ (norm_nonneg _) hn 2
      · have hfz : f z=0 := notMem_support.mp (fun h => hz (hfs h))
        have hgz : compactMollification (testMollifier n) f hf hc z=0 :=
          notMem_support.mp (fun h => hz (hgs n h))
        simp only [Set.indicator_of_notMem hz,hfz,hgz,sub_self,norm_zero,zero_pow (by decide : 2≠0),le_refl])
    (by
      filter_upwards [compactMollification_ae_tendsto f hf hc] with z hz
      simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using (hz.sub_const (f z)).norm.pow 2)
  simpa only [integral_zero] using h

theorem compactMollification_Lp_tendsto (f : (ℝ×ℝ) → ℂ)
    (hfm : Measurable f) (hf : Integrable f planeMeasure) (hc : HasCompactSupport f)
    (hb : ∀ z, ‖f z‖≤1) (hf2 : MemLp f 2 planeMeasure) :
    Tendsto (fun n => (compactMollification (testMollifier n) f hf hc).toLp 2 planeMeasure)
      atTop (nhds (hf2.toLp f)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => compactMollification (testMollifier n) f hf hc)
    (fun n => (compactMollification (testMollifier n) f hf hc).memLp 2 planeMeasure) f hf2).mpr
  have he (n : ℕ) : eLpNorm ((compactMollification (testMollifier n) f hf hc : (ℝ×ℝ) → ℂ)-f) 2 planeMeasure=
      ENNReal.ofReal (Real.sqrt (∫ z, ‖compactMollification (testMollifier n) f hf hc z-f z‖^2 ∂planeMeasure)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      (((compactMollification (testMollifier n) f hf hc).memLp 2 planeMeasure).sub hf2)]
    norm_num [Real.sqrt_eq_rpow]
  simp_rw [he]
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp (compactMollification_energy_tendsto f hfm hf hc hb))
  simpa only [Function.comp_def,Real.sqrt_zero,ENNReal.ofReal_zero] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
