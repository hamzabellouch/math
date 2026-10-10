import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationDatumRegularity

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem continuous_average_ae_of_ball_bounds {f : Ω → Position → ℝ}
    (hf : ∀ᵐ o ∂μ, Continuous (f o)) (hm : Measurable (Function.uncurry f))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C) :
    Continuous (fun x => ∫ o, f o x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨C,hC⟩ := hb (‖x₀‖+1)
  apply continuousAt_of_dominated
    (Eventually.of_forall (fun x => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable))
    (bound := fun _ => C) ?_ (integrable_const C)
    (hf.mono (fun o ho => ho.continuousAt))
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
  filter_upwards [] with o
  have hdist : ‖x-x₀‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hn : ‖x‖≤‖x₀‖+1 := by
    have h := norm_add_le (x-x₀) x₀
    rw [sub_add_cancel] at h
    linarith
  change ‖f o x‖ ≤ C
  simpa only [Real.norm_eq_abs] using hC o x (by simpa using hn)

theorem WeakNuclearSubsolution.average_ae {f q : Ω → Position → ℝ} {Z : ℝ} {U : Set Position}
    (hf : ∀ᵐ o ∂μ, Continuous (f o))
    (hcf : Continuous (fun x => ∫ o, f o x ∂μ))
    (hmf : Measurable (Function.uncurry f)) (hmq : Measurable (Function.uncurry q))
    (hbf : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |q o x| ≤ C)
    (hw : ∀ᵐ o ∂μ, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f o x) Z U (q o)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+∫ o, f o x ∂μ) Z U
      (fun x => ∫ o, q o x ∂μ) := by
  apply (weakNuclearSubsolution_offset_iff hcf).2
  apply WeakLaplacianGE.average hmf hmq hbf hbq
  filter_upwards [hw,hf] with o ho hf
  exact (weakNuclearSubsolution_offset_iff hf).1 ho

theorem WeakNuclearSubsolution.average_cutoffTF_ae {a Z : ℝ} {U : Set Position}
    {f b : Ω → Position → ℝ} (ha : 0<a)
    (hf : ∀ᵐ o ∂μ, Continuous (f o))
    (hmf : Measurable (Function.uncurry f)) (hmb : Measurable (Function.uncurry b))
    (hbf : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (hbb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |b o x| ≤ C)
    (hw : ∀ᵐ o ∂μ, WeakNuclearSubsolution (fun x => Z*coulombKernel x+f o x) Z U
      (fun x => b o x+cutoffReaction a (fun y => Z*coulombKernel y+f o y) x)) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x+∫ o, f o x ∂μ) Z U
      (fun x => (∫ o, b o x ∂μ)+cutoffReaction a (fun y => Z*coulombKernel y+∫ o, f o y ∂μ) x) := by
  let q : Ω → Position → ℝ := fun o x => b o x+cutoffReaction a (fun y => Z*coulombKernel y+f o y) x
  have hmq : Measurable (Function.uncurry q) := hmb.add (cutoffReaction_offset_joint_measurable hmf)
  have hbc := cutoffReaction_offset_uniform_bound (Z:=Z) ha hbf
  have hbq : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |q o x| ≤ C := by
    intro R
    obtain ⟨C,hC⟩ := hbb R
    obtain ⟨D,hD⟩ := hbc R
    exact ⟨C+D,fun o x hx => (abs_add_le _ _).trans (add_le_add (hC o x hx) (hD o x hx))⟩
  have hc := continuous_average_ae_of_ball_bounds (μ:=μ) hf hmf hbf
  have H := WeakNuclearSubsolution.average_ae hf hc hmf hmq hbf hbq hw
  apply (weakNuclearSubsolution_offset_iff hc).2
  apply ((weakNuclearSubsolution_offset_iff hc).1 H).mono_source_on
  · exact locallyIntegrable_of_ball_bounds hmq.stronglyMeasurable.integral_prod_left.measurable
      (average_ball_bounds (μ:=μ) hbq)
  · exact (locallyIntegrable_of_ball_bounds hmb.stronglyMeasurable.integral_prod_left.measurable
      (average_ball_bounds (μ:=μ) hbb)).add (cutoffReaction_offset_locallyIntegrable ha hc)
  · filter_upwards [] with x hx
    have hib := integrable_section_of_ball_bounds (μ:=μ) hmb hbb x
    have hic := integrable_section_of_ball_bounds (μ:=μ)
      (f:=fun o x => cutoffReaction a (fun y => Z*coulombKernel y+f o y) x)
      (cutoffReaction_offset_joint_measurable hmf) hbc x
    change (∫ o, b o x ∂μ)+cutoffReaction a (fun y => Z*coulombKernel y+∫ o, f o y ∂μ) x ≤
      ∫ o, b o x+cutoffReaction a (fun y => Z*coulombKernel y+f o y) x ∂μ
    rw [integral_add hib hic]
    have h := cutoffReaction_average_le (μ:=μ) (a:=a) (Z:=Z) hmf hbf x
    linarith

end Average
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {u μ p : Ω → Position → ℝ} {B C r Z L : ℝ}
theorem PropagationInvariant.average_ae (hr : 0<r)
    (hi : ∀ᵐ o ∂P,PropagationInvariant B C r Z L (u o) (μ o) (p o))
    (hu : Measurable (Function.uncurry u)) (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p))
    (hbu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hbp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    PropagationInvariant B C r Z L (fun x => ∫ o,u o x ∂P)
      (fun x => ∫ o,μ o x ∂P) (fun x => ∫ o,p o x ∂P) := by
  constructor
  · exact continuous_average_ae_of_ball_bounds (hi.mono (fun o ho => ho.continuous_offset)) hu hbu
  · intro x
    exact integral_nonneg_of_ae (hi.mono (fun o ho => ho.nonnegative_error x))
  · intro x hx
    exact integral_eq_zero_of_ae (hi.mono (fun o ho => ho.error_support x hx))
  · have H := WeakNuclearSubsolution.average_cutoffTF_ae (μ:=P) (Z:=Z)
      (b:=fun o x => propagationCoreSource r ‖x‖ (μ o x) (p o x)) hr
      (hi.mono (fun o ho => ho.continuous_offset)) hu (propagationCoreSource_joint_measurable (r:=r) hμ hp)
      hbu (propagationCoreSource_uniform_bounds (r:=r) hbμ hbp)
      (hi.mono (fun o ho => by simpa only [propagationRHS_eq] using ho.weak))
    simp only [propagationCoreSource_average hμ hp hbμ hbp] at H
    simpa only [propagationRHS,cutoffReaction,Set.indicator,Set.mem_ofPred_eq] using H
  · intro x hx
    have hiu := integrable_section_of_ball_bounds (μ:=P) hu hbu x
    have hii := (integrable_const (Z*coulombKernel x)).add hiu
    have he : (∫ o,Z*coulombKernel x+u o x ∂P)=Z*coulombKernel x+∫ o,u o x ∂P := by
      rw [integral_add (integrable_const _) hiu]; simp
    constructor
    · have H := integral_mono_ae (integrable_const (propagationBarrier B r x)) hii
        (hi.mono (fun o ho => (ho.caps x hx).1))
      change (∫ _ : Ω,propagationBarrier B r x ∂P) ≤ (∫ o,Z*coulombKernel x+u o x ∂P) at H
      simpa only [integral_const,probReal_univ,one_smul,he] using H
    · have H := integral_mono_ae hii (integrable_const (C/‖x‖^4))
        (hi.mono (fun o ho => (ho.caps x hx).2))
      change (∫ o,Z*coulombKernel x+u o x ∂P) ≤ (∫ _ : Ω,C/‖x‖^4 ∂P) at H
      simpa only [integral_const,probReal_univ,one_smul,he] using H
  · intro x hx
    have hiu := integrable_section_of_ball_bounds (μ:=P) hu hbu x
    have he : (∫ o,Z*coulombKernel x+u o x ∂P)=Z*coulombKernel x+∫ o,u o x ∂P := by
      rw [integral_add (integrable_const _) hiu]; simp
    rw [←he]
    calc
      _ = ∫ _ : Ω,propagationBarrier B r x ∂P := integral_congr_ae (hi.mono (fun o ho => ho.outer x hx))
      _ = _ := by simp
end Average
end NeutralAtom
end

end

end OAI
