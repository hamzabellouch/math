import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.InitialInvariant
import OAI.Analysis.CoulombRadii.RandomFields.CompactRandomField

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Init
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {bad : Ω → Prop} {H μ : Ω → Position → ℝ} {B C Z r a L : ℝ}
lemma initialPropagationOffset_joint_measurable (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Ω×Position => initialPropagationOffset (bad z.1) Z r a (H z.1) z.2) := by
  exact ((measurable_const.ite (hb.preimage measurable_fst) hH).sub measurable_const).add
    (measurable_const.mul ((continuous_norm.measurable.comp measurable_snd).pow_const 2))

omit [MeasurableSpace Ω] in
lemma initialPropagationOffset_uniform_bounds
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A) :
    ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |initialPropagationOffset (bad o) Z r a (H o) x|≤A := by
  intro D
  obtain ⟨K,hK⟩ := hbH D
  refine ⟨max 0 K+|(7/10:ℝ)*Z/r|+|a| * D^2,fun o x hx => ?_⟩
  have hn : ‖x‖≤D := by simpa using hx
  have h2 : ‖x‖^2≤D^2 := pow_le_pow_left₀ (norm_nonneg x) hn 2
  have hi : |if bad o then (0:ℝ) else H o x| ≤ max 0 K := by
    split_ifs
    · simpa only [abs_zero] using le_max_left 0 K
    · exact (hK o x hx).trans (le_max_right 0 K)
  exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hi le_rfl))
    (by rw [abs_mul,abs_of_nonneg (sq_nonneg ‖x‖)]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg a)))

lemma initialNextOffset_joint_measurable (hr : 0<r) (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Ω×Position => initialNextOffset (bad z.1) B Z r a (H z.1) z.2) :=
  radialMaxSplice_joint_measurable (f:=fun o => initialPropagationOffset (bad o) Z r a (H o))
    (g:=fun _ => propagationBarrierOffset B r Z) ((103/100)*r) ((39/20)*r)
    (initialPropagationOffset_joint_measurable hb hH)
    ((propagationBarrierOffset_continuous B Z hr).measurable.comp measurable_snd)

omit [MeasurableSpace Ω] in
lemma initialNextOffset_uniform_bounds (hr : 0<r)
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A) :
    ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |initialNextOffset (bad o) B Z r a (H o) x|≤A := by
  intro D
  obtain ⟨K,hK⟩ := initialPropagationOffset_uniform_bounds (bad:=bad) (Z:=Z) (r:=r) (a:=a) hbH D
  obtain ⟨A,hA⟩ := continuous_ball_bounds (propagationBarrierOffset_continuous B Z hr) D
  exact ⟨max K A,fun o x hx => radialMaxSplice_abs_bound (hK o x hx) (hA x hx)⟩

lemma initialPropagationError_joint_measurable (hb : MeasurableSet {o | bad o})
    (hμ : Measurable (Function.uncurry μ)) :
    Measurable (fun z : Ω×Position => initialPropagationError (bad z.1) r (μ z.1) z.2) :=
  hμ.ite ((hb.preimage measurable_fst).inter (measurableSet_lt
    (continuous_norm.measurable.comp measurable_snd) measurable_const)) measurable_const

omit [MeasurableSpace Ω] in
lemma initialPropagationError_uniform_bounds
    (hbμ : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤A) :
    ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |initialPropagationError (bad o) r (μ o) x|≤A := by
  intro D
  obtain ⟨K,hK⟩ := hbμ D
  refine ⟨max K 0,fun o x hx => ?_⟩
  unfold initialPropagationError
  split_ifs
  · exact (hK o x hx).trans (le_max_left K 0)
  · simpa only [abs_zero] using le_max_right K 0

def initialPropagationDatum (hr : 0<r) (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) (hμ : Measurable (Function.uncurry μ))
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A)
    (hbμ : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤A)
    (hd : ∀ᵐ o ∂P,InitialPropagationData (bad o) B C Z r a L (H o) (μ o)) :
    PropagationDatum P B C r Z L μ :=
  ⟨fun o => initialNextOffset (bad o) B Z r a (H o),fun o => initialPropagationError (bad o) r (μ o),
    initialNextOffset_joint_measurable hr hb hH,initialPropagationError_joint_measurable hb hμ,
    initialNextOffset_uniform_bounds hr hbH,initialPropagationError_uniform_bounds hbμ,
    hd.mono (fun _ h => h.invariant)⟩
end Init
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Error
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {μ p : Ω → Position → ℝ} {bad : Ω → Prop} {r R : ℝ}

lemma shell_error_product_integrable (hm : Measurable (Function.uncurry μ))
    (hb : MeasurableSet {o | bad o})
    (hbm : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C) :
    Integrable (fun z : Ω×Position => if bad z.1 ∧ r≤‖z.2‖ ∧ ‖z.2‖<R then μ z.1 z.2 else 0) (P.prod volume) := by
  apply compact_random_field_integrable (P:=P) (f:=fun o x => if bad o ∧ r≤‖x‖ ∧ ‖x‖<R then μ o x else 0) (R:=R)
    (hm.ite ((hb.preimage measurable_fst).inter
      ((measurableSet_le measurable_const (continuous_norm.measurable.comp measurable_snd)).inter
      (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const))) measurable_const)
  · intro D; obtain ⟨C,hC⟩ := hbm D
    refine ⟨max C 0,fun o x hx => ?_⟩
    split_ifs
    · exact (hC o x hx).trans (le_max_left _ _)
    · simpa only [abs_zero] using le_max_right C 0
  · exact Eventually.of_forall (fun o x hx => ite_eq_right (fun h => (not_lt.mpr hx) h.2.2))

lemma propagationStepError_total (hm : Measurable (Function.uncurry μ))
    (hb : MeasurableSet {o | bad o})
    (hbm : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hip : Integrable (Function.uncurry p) (P.prod volume)) :
    (∫ o,(∫ x,propagationStepError (bad o) r R ‖x‖ (μ o x) (p o x)) ∂P)=
      (∫ o,(∫ x,p o x) ∂P)+(∫ o in {o | bad o},∫ x in {x : Position | r≤‖x‖ ∧ ‖x‖<R},μ o x ∂volume ∂P) := by
  let f := fun o x => if bad o ∧ r≤‖x‖ ∧ ‖x‖<R then μ o x else 0
  have hi := shell_error_product_integrable (P:=P) (r:=r) (R:=R) hm hb hbm
  have he : ∀ o,(∫ x,f o x)={o | bad o}.indicator
      (fun o => ∫ x in {x : Position | r≤‖x‖ ∧ ‖x‖<R},μ o x) o := by
    intro o
    by_cases ho : bad o
    · rw [Set.indicator_of_mem (s:={o | bad o}) ho]
      have hS : MeasurableSet {x : Position | r≤‖x‖ ∧ ‖x‖<R} :=
        (measurableSet_le measurable_const continuous_norm.measurable).inter
          (measurableSet_lt continuous_norm.measurable measurable_const)
      rw [←integral_indicator hS]
      apply integral_congr_ae (Eventually.of_forall (fun x => ?_))
      simp only [f,ho,true_and,Set.indicator_apply,mem_ofPred_eq]
    · simp only [f,ho,false_and,ite_false,integral_zero,Set.indicator_of_notMem (s:={o | bad o}) ho]
  change (∫ o,(∫ x,p o x+f o x) ∂P)=_
  have hie : Integrable (Function.uncurry f) (P.prod volume) := hi
  have hiadd : Integrable (fun z : Ω×Position => p z.1 z.2+f z.1 z.2) (P.prod volume) := hip.add hie
  rw [←integral_prod _ hiadd]
  change (∫ z,(Function.uncurry p z + Function.uncurry f z) ∂P.prod volume)=_
  rw [integral_add hip hie,integral_prod _ hip,integral_prod _ hie]
  congr 1
  change (∫ o,(∫ x,f o x) ∂P)=_
  simp_rw [he]
  exact integral_indicator hb

omit [IsProbabilityMeasure P] in
lemma initialPropagationError_total (_ : Measurable (Function.uncurry μ))
    (hb : MeasurableSet {o | bad o}) :
    (∫ o,(∫ x,initialPropagationError (bad o) r (μ o) x) ∂P)=
      ∫ o in {o | bad o},∫ x in Metric.ball (0:Position) r,μ o x ∂volume ∂P := by
  rw [←integral_indicator hb]
  apply integral_congr_ae (Eventually.of_forall (fun o => ?_))
  by_cases ho : bad o
  · rw [Set.indicator_of_mem (s:={o | bad o}) ho,←integral_indicator measurableSet_ball]
    apply integral_congr_ae (Eventually.of_forall (fun x => ?_))
    simp [initialPropagationError,ho,Set.indicator_apply,Metric.mem_ball]
  · simp [initialPropagationError,ho]
end Error
end NeutralAtom
end

end

end OAI
