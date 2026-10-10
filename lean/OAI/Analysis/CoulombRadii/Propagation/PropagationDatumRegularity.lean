import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalPosteriorInverse
import OAI.Analysis.CoulombRadii.Propagation.PropagationAverage
import OAI.Analysis.CoulombRadii.Propagation.PropagationStepWeak

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma continuous_ball_bounds {f : Position → ℝ} (hf : Continuous f) :
    ∀ D : ℝ,∃ C : ℝ,∀ x∈Metric.closedBall 0 D,|f x|≤C := by
  intro D
  simpa only [Real.norm_eq_abs] using
    (isCompact_closedBall (0:Position) D).exists_bound_of_continuousOn hf.continuousOn

section Datum
variable {Ω : Type*} [MeasurableSpace Ω] {bad : Ω → Prop}
variable {u H μ p : Ω → Position → ℝ} {B r R Z L l1 l2 : ℝ}

lemma propagationPairOffset_joint_measurable (hb : MeasurableSet {o | bad o})
    (hu : Measurable (Function.uncurry u)) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Ω×Position => propagationPairOffset (bad z.1) R l1 l2 (u z.1) (H z.1) z.2) := by
  exact (hu.sub measurable_const).ite (hb.preimage measurable_fst)
    ((hu.sub measurable_const).max (hH.sub measurable_const))

omit [MeasurableSpace Ω] in
lemma propagationPairOffset_uniform_bounds
    (hu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hH : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |propagationPairOffset (bad o) R l1 l2 (u o) (H o) x|≤C := by
  intro D
  obtain ⟨C,hC⟩ := hu D
  obtain ⟨A,hA⟩ := hH D
  refine ⟨max (C+|l1/R^4|) (A+|l2/R^4|),?_⟩
  intro o x hx
  have h1 := (abs_sub (u o x) (l1/R^4)).trans (add_le_add (hC o x hx) le_rfl)
  have h2 := (abs_sub (H o x) (l2/R^4)).trans (add_le_add (hA o x hx) le_rfl)
  unfold propagationPairOffset
  split_ifs
  · exact h1.trans (le_max_left _ _)
  · exact abs_max_le_max_abs_abs.trans (max_le_max h1 h2)

lemma propagationNextOffset_joint_measurable (hR : 0<R) (hb : MeasurableSet {o | bad o})
    (hu : Measurable (Function.uncurry u)) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun z : Ω×Position => propagationNextOffset (bad z.1) B R Z L l1 l2 (u z.1) (H z.1) z.2) :=
  radialMaxSplice_joint_measurable (f:=fun o => propagationPairOffset (bad o) R l1 l2 (u o) (H o))
    (g:=fun _ => propagationBarrierOffset B R Z) ((53/50)*R) ((3/2)*L*R) (propagationPairOffset_joint_measurable hb hu hH)
    ((propagationBarrierOffset_continuous B Z hR).measurable.comp measurable_snd)

omit [MeasurableSpace Ω] in
lemma propagationNextOffset_uniform_bounds (hR : 0<R)
    (hu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hH : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |propagationNextOffset (bad o) B R Z L l1 l2 (u o) (H o) x|≤C := by
  intro D
  obtain ⟨C,hC⟩ := propagationPairOffset_uniform_bounds (bad:=bad) (R:=R) (l1:=l1) (l2:=l2) hu hH D
  obtain ⟨A,hA⟩ := continuous_ball_bounds (propagationBarrierOffset_continuous B Z hR) D
  exact ⟨max C A,fun o x hx => radialMaxSplice_abs_bound (hC o x hx) (hA x hx)⟩

lemma propagationStepError_joint_measurable (hb : MeasurableSet {o | bad o})
    (hμ : Measurable (Function.uncurry μ)) (hp : Measurable (Function.uncurry p)) :
    Measurable (fun z : Ω×Position => propagationStepError (bad z.1) r R ‖z.2‖ (μ z.1 z.2) (p z.1 z.2)) := by
  apply hp.add
  exact hμ.ite ((hb.preimage measurable_fst).inter
    ((measurableSet_le measurable_const (continuous_norm.measurable.comp measurable_snd)).inter
      (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const))) measurable_const

omit [MeasurableSpace Ω] in
lemma propagationStepError_uniform_bounds
    (hμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |propagationStepError (bad o) r R ‖x‖ (μ o x) (p o x)|≤C := by
  intro D
  obtain ⟨C,hC⟩ := hμ D
  obtain ⟨A,hA⟩ := hp D
  refine ⟨A+max C 0,?_⟩
  intro o x hx
  apply (abs_add_le _ _).trans
  apply add_le_add (hA o x hx)
  split_ifs
  · exact (hC o x hx).trans (le_max_left _ _)
  · simp
end Datum
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma atomic_screenedField_nuclear {ρ : Position → ℝ} (hi : Integrable ρ)
    (hc : Continuous (potentialOf ρ)) (Z : ℝ) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x-potentialOf ρ x) Z univ
      (fun x => 4*Real.pi*ρ x) := by
  change WeakNuclearSubsolution (fun x => Z*coulombKernel x+(-potentialOf ρ x)) Z univ _
  apply (weakNuclearSubsolution_offset_iff hc.neg).2
  intro φ hφ hφc ht hp
  have H := potentialOf_weakLaplacian hi φ hφ hφc ht
  have H' : (∫ x,(-potentialOf ρ x)*coordinateLaplacian φ x)=
      ∫ x,(4*Real.pi*ρ x)*φ x := by
    simp only [neg_mul,integral_neg] at H ⊢
    rw [H]
    simp only [neg_neg]
  exact H'.ge

lemma conditionalPacketField_nuclear {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (datum : A) (Z : ℝ) :
    WeakNuclearSubsolution (fun x => Z*coulombKernel x-potentialOf
      (conditionalPacketDensity P raw obs g c r₀ s datum) x) Z univ
      (fun x => 4*Real.pi*conditionalPacketDensity P raw obs g c r₀ s datum x) :=
  atomic_screenedField_nuclear (mixturePacketDensity_integrable hg hm hc hr hs _)
    (conditionalPacketPotential_continuous P raw obs hg hgs hm hc hr hs datum) Z
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure PropagationInvariant (B C r Z L : ℝ) (u μ p : Position → ℝ) : Prop where
  continuous_offset : Continuous u
  nonnegative_error : ∀ x,0≤p x
  error_support : ∀ x,r≤‖x‖ → p x=0
  weak : WeakNuclearSubsolution (fun x => Z*coulombKernel x+u x) Z univ
    (fun x => propagationRHS r ‖x‖ (μ x) (p x) (Z*coulombKernel x+u x))
  caps : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
    Z*coulombKernel x+u x≤C/‖x‖^4
  outer : ∀ x,L*r<‖x‖ → Z*coulombKernel x+u x=propagationBarrier B r x

lemma PropagationStepHypotheses.next_invariant
    {bad : Prop} {B C r R Z L l1 l2 e ξ hl hh : ℝ} {u H μ p : Position → ℝ}
    (d : PropagationStepHypotheses bad B C r R Z L l1 l2 e ξ hl hh u H μ p)
    (hs : ∀ x,r≤‖x‖ → p x=0) :
    PropagationInvariant B C R Z L (propagationNextOffset bad B R Z L l1 l2 u H) μ
      (fun x => propagationStepError bad r R ‖x‖ (μ x) (p x)) :=
  ⟨d.next_continuous,d.next_error_nonneg,d.next_error_support hs,d.next_weak,
    fun _ => d.next_caps,fun _ => d.next_outer⟩

section Average
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {u μ p : Ω → Position → ℝ} {B C r Z L : ℝ}

lemma propagationCoreSource_joint_measurable
    (hμ : Measurable (Function.uncurry μ)) (hp : Measurable (Function.uncurry p)) :
    Measurable (fun z : Ω×Position => propagationCoreSource r ‖z.2‖ (μ z.1 z.2) (p z.1 z.2)) :=
  measurable_const.mul ((hμ.ite (measurableSet_lt
    (continuous_norm.measurable.comp measurable_snd) measurable_const) measurable_const).sub hp)

omit [MeasurableSpace Ω] in
lemma propagationCoreSource_uniform_bounds
    (hμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D →
      |propagationCoreSource r ‖x‖ (μ o x) (p o x)|≤C := by
  intro D
  obtain ⟨A,hA⟩ := hμ D
  obtain ⟨K,hK⟩ := hp D
  exact ⟨4*Real.pi*(A+K),fun o x hx => propagationCoreSource_abs_bound (hA o x hx) (hK o x hx)⟩

lemma propagationCoreSource_average (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p))
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hbp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) (x : Position) :
    (∫ o,propagationCoreSource r ‖x‖ (μ o x) (p o x) ∂P)=
      propagationCoreSource r ‖x‖ (∫ o,μ o x ∂P) (∫ o,p o x ∂P) := by
  obtain h1 := integrable_section_of_ball_bounds (μ:=P) hμ hbμ x
  obtain h2 := integrable_section_of_ball_bounds (μ:=P) hp hbp x
  unfold propagationCoreSource
  split_ifs
  · rw [integral_const_mul,integral_sub h1 h2]
  · simp only [zero_sub,integral_const_mul,integral_neg]

theorem PropagationInvariant.average (hr : 0<r)
    (hi : ∀ o,PropagationInvariant B C r Z L (u o) (μ o) (p o))
    (hu : Measurable (Function.uncurry u)) (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p))
    (hbu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hbp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    PropagationInvariant B C r Z L (fun x => ∫ o,u o x ∂P)
      (fun x => ∫ o,μ o x ∂P) (fun x => ∫ o,p o x ∂P) := by
  constructor
  · exact continuous_average_of_ball_bounds (fun o => (hi o).continuous_offset) hu hbu
  · intro x
    exact integral_nonneg (fun o => (hi o).nonnegative_error x)
  · intro x hx
    simp only [(hi _).error_support x hx,integral_zero]
  · have H := WeakNuclearSubsolution.average_cutoffTF (μ:=P) (Z:=Z)
      (b:=fun o x => propagationCoreSource r ‖x‖ (μ o x) (p o x)) hr
      (fun o => (hi o).continuous_offset) hu (propagationCoreSource_joint_measurable (r:=r) hμ hp)
      hbu (propagationCoreSource_uniform_bounds (r:=r) hbμ hbp)
      (Eventually.of_forall (fun o => by simpa only [propagationRHS_eq] using (hi o).weak))
    simp only [propagationCoreSource_average hμ hp hbμ hbp] at H
    simpa only [propagationRHS,cutoffReaction,Set.indicator,Set.mem_ofPred_eq] using H
  · intro x hx
    have hiu := integrable_section_of_ball_bounds (μ:=P) hu hbu x
    have hii := (integrable_const (Z*coulombKernel x)).add hiu
    have he : (∫ o,Z*coulombKernel x+u o x ∂P)=Z*coulombKernel x+∫ o,u o x ∂P := by
      rw [integral_add (integrable_const _) hiu]; simp
    constructor
    · have H := integral_mono (integrable_const (propagationBarrier B r x)) hii
        (fun o => ((hi o).caps x hx).1)
      change (∫ _ : Ω,propagationBarrier B r x ∂P) ≤ (∫ o,Z*coulombKernel x+u o x ∂P) at H
      simpa only [integral_const,probReal_univ,one_smul,he] using H
    · have H := integral_mono hii (integrable_const (C/‖x‖^4))
        (fun o => ((hi o).caps x hx).2)
      change (∫ o,Z*coulombKernel x+u o x ∂P) ≤ (∫ _ : Ω,C/‖x‖^4 ∂P) at H
      simpa only [integral_const,probReal_univ,one_smul,he] using H
  · intro x hx
    have hiu := integrable_section_of_ball_bounds (μ:=P) hu hbu x
    have he : (∫ o,Z*coulombKernel x+u o x ∂P)=Z*coulombKernel x+∫ o,u o x ∂P := by
      rw [integral_add (integrable_const _) hiu]; simp
    rw [←he]
    simp only [(hi _).outer x hx,integral_const,probReal_univ,one_smul]
end Average
end NeutralAtom
end

end

end OAI
