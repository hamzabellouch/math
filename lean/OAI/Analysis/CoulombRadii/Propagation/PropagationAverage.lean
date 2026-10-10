import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.WeakLocality

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom
section Average
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_section_of_ball_bounds {f : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry f))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (x : Position) : Integrable (fun o => f o x) μ := by
  obtain ⟨C,hC⟩ := hb ‖x‖
  apply (integrable_const C).mono' (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [] with o
  change ‖f o x‖ ≤ C
  simpa only [Real.norm_eq_abs] using hC o x (by simp)

lemma average_ball_bounds {f : Ω → Position → ℝ}
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ x ∈ Metric.closedBall 0 R, |∫ o, f o x ∂μ| ≤ C := by
  intro R
  obtain ⟨C,hC⟩ := hb R
  refine ⟨C,fun x hx => ?_⟩
  calc
    |∫ o, f o x ∂μ| ≤ ∫ o, |f o x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Ω, C ∂μ := integral_mono_of_nonneg
      (Eventually.of_forall (fun o => abs_nonneg (f o x))) (integrable_const C)
      (Eventually.of_forall (fun o => hC o x hx))
    _ = C := by simp

theorem continuous_average_of_ball_bounds {f : Ω → Position → ℝ}
    (hf : ∀ o, Continuous (f o)) (hm : Measurable (Function.uncurry f))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C) :
    Continuous (fun x => ∫ o, f o x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨C,hC⟩ := hb (‖x₀‖+1)
  apply continuousAt_of_dominated
    (Eventually.of_forall (fun x => (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable))
    (bound := fun _ => C) ?_ (integrable_const C)
    (Eventually.of_forall (fun o => (hf o).continuousAt))
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0:ℝ)<1)] with x hx
  filter_upwards [] with o
  have hdist : ‖x-x₀‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hn : ‖x‖≤‖x₀‖+1 := by
    have h := norm_add_le (x-x₀) x₀
    rw [sub_add_cancel] at h
    linarith
  change ‖f o x‖ ≤ C
  simpa only [Real.norm_eq_abs] using hC o x (by simpa using hn)

omit [MeasurableSpace Ω] in
lemma cutoffReaction_offset_uniform_bound {a Z : ℝ} (ha : 0<a) {f : Ω → Position → ℝ}
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C) :
    ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R →
      |cutoffReaction a (fun y => Z*coulombKernel y+f o y) x| ≤ C := by
  intro R
  obtain ⟨D,hD⟩ := hb R
  refine ⟨tfReaction (|Z|/a+D),?_⟩
  intro o x hx
  by_cases haX : a ≤ ‖x‖
  · have hn : 0 < ‖x‖ := ha.trans_le haX
    have hZ : Z*coulombKernel x ≤ |Z|/a := by
      unfold coulombKernel
      calc
        Z*‖x‖⁻¹ ≤ |Z| *‖x‖⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) (inv_nonneg.mpr hn.le)
        _ ≤ |Z| *a⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ ha haX) (abs_nonneg _)
        _ = |Z|/a := by rw [div_eq_mul_inv]
    have h := tfReaction_monotone (show Z*coulombKernel x+f o x ≤ |Z|/a+D by
      have H : f o x ≤ D := (le_abs_self _).trans (hD o x hx)
      linarith)
    simpa [cutoffReaction, haX, abs_of_nonneg (tfReaction_nonneg _)] using h
  · simpa [cutoffReaction, haX] using tfReaction_nonneg (|Z|/a+D)

lemma cutoffReaction_offset_joint_measurable {a Z : ℝ} {f : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry f)) :
    Measurable (fun z : Ω × Position => cutoffReaction a (fun y => Z*coulombKernel y+f z.1 y) z.2) := by
  have h : Measurable (fun z : Ω × Position => tfReaction (Z*coulombKernel z.2+f z.1 z.2)) :=
    tfReaction_continuous.measurable.comp ((measurable_const.mul
    (measurable_coulombKernel.comp measurable_snd)).add hm)
  exact h.ite ((isClosed_le continuous_const continuous_norm).measurableSet.preimage measurable_snd)
    measurable_const

lemma cutoffReaction_average_le {a Z : ℝ} {f : Ω → Position → ℝ}
    (hm : Measurable (Function.uncurry f))
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ o x, x ∈ Metric.closedBall 0 R → |f o x| ≤ C)
    (x : Position) :
    cutoffReaction a (fun y => Z*coulombKernel y+∫ o, f o y ∂μ) x ≤
      ∫ o, cutoffReaction a (fun y => Z*coulombKernel y+f o y) x ∂μ := by
  by_cases haX : a ≤ ‖x‖
  · simp only [cutoffReaction, Set.indicator, Set.mem_ofPred_eq, haX, ↓reduceIte]
    have hi := integrable_section_of_ball_bounds (μ:=μ) hm hb x
    have hi' : Integrable (fun o => Z*coulombKernel x+f o x) μ :=
      (integrable_const (Z*coulombKernel x)).add hi
    have hpow : Integrable (fun o => (max (Z*coulombKernel x+f o x) 0)^(3/2:ℝ)) μ := by
      obtain ⟨C,hC⟩ := hb ‖x‖
      have hB : 0≤|Z*coulombKernel x|+max C 0 := add_nonneg (abs_nonneg _) (le_max_right _ _)
      apply (integrable_const ((|Z*coulombKernel x|+max C 0)^(3/2:ℝ))).mono'
        ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).measurable.comp
          (((measurable_const.add (hm.comp (measurable_id.prodMk measurable_const))).max measurable_const))).aestronglyMeasurable
      filter_upwards [] with o
      change ‖(max (Z*coulombKernel x+f o x) 0)^(3/2:ℝ)‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
      apply Real.rpow_le_rpow (le_max_right _ _) _ (by norm_num)
      apply max_le _ hB
      have H := hC o x (by simp)
      linarith [le_abs_self (Z*coulombKernel x),le_abs_self (f o x), le_max_left C 0]
    have H := tfReaction_integral_le hi' hpow
    simpa [integral_add (integrable_const _) hi] using H
  · simp [cutoffReaction,haX]

theorem WeakNuclearSubsolution.average_cutoffTF {a Z : ℝ} {U : Set Position}
    {f b : Ω → Position → ℝ} (ha : 0<a)
    (hf : ∀ o, Continuous (f o))
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
  have hc := continuous_average_of_ball_bounds (μ:=μ) hf hmf hbf
  have H := WeakNuclearSubsolution.average hf hc hmf hmq hbf hbq hw
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

end OAI
