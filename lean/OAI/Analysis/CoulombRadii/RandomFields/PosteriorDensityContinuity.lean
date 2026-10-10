import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationAverageAE

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
lemma mixturePacketDensity_continuous {n : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) {c r s : ℝ}
    (hc : 0<c) (hr : 0<r) (hs : 0<s) : Continuous (mixturePacketDensity ν g c r s) := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  change Continuous (fun x => ∫ o,rawPacketDensity g c r s o x ∂ν)
  have hb : ∀ D : ℝ,∃ C : ℝ,∀ (o : Configuration n) x,x∈Metric.closedBall 0 D → |rawPacketDensity g c r s o x|≤C := by
    intro D
    refine ⟨n*((c*r*(min r s)^packetExponent)^(-3:ℤ)*A),fun o x _ => ?_⟩
    rw [abs_of_nonneg (rawPacketDensity_nonneg g hc hr hs o x)]
    exact rawPacketDensity_bound hA hAb hc hr hs o x
  have hj : Continuous (fun z : Configuration n×Position => rawPacketDensity g c r s z.1 z.2) :=
    continuous_rawPacketDensity hg hc hr hs
  have hx : ∀ o : Configuration n,Continuous (rawPacketDensity g c r s o) := by
    intro o
    exact Continuous.uncurry_left (f:=rawPacketDensity g c r s) o hj
  exact continuous_average_of_ball_bounds (μ:=ν) (f:=fun (o : Configuration n) (x : Position) => rawPacketDensity g c r s o x) hx hj.measurable hb

lemma conditionalPacketDensity_continuous {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) {c r s : ℝ}
    (hc : 0<c) (hr : 0<r) (hs : 0<s) (a : A) :
    Continuous (conditionalPacketDensity P raw obs g c r s a) :=
  mixturePacketDensity_continuous _ hg hgs hc hr hs

lemma measurable_conditionalPacketDensity_joint {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → A)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) {c r s : ℝ}
    (hc : 0<c) (hr : 0<r) (hs : 0<s) :
    Measurable (fun z : A×Position => conditionalPacketDensity P raw obs g c r s z.1 z.2) := by
  have H : Measurable (fun z : Position×A => conditionalPacketDensity P raw obs g c r s z.2 z.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (conditionalPacketDensity_continuous P raw obs hg hgs hc hr hs)
      (measurable_conditionalPacketDensity_data P raw obs hg hc hr hs)
  exact H.comp measurable_swap
end NeutralAtom
end

end
section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Posterior
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable (P : Measure Ω) [IsProbabilityMeasure P] (obs : Ω → A)

def posteriorAverage (f : Ω → Position → ℝ) (a : A) (x : Position) : ℝ :=
  ∫ o,f o x ∂ProbabilityTheory.condDistrib id obs P a
lemma posteriorAverage_joint_measurable {f : Ω → Position → ℝ}
    (hf : Measurable (Function.uncurry f)) : Measurable (Function.uncurry (posteriorAverage P obs f)) := by
  let κ : ProbabilityTheory.Kernel (A×Position) Ω := (ProbabilityTheory.condDistrib id obs P).comap (Prod.fst : A×Position → A) measurable_fst
  have H : StronglyMeasurable (fun z : (A×Position)×Ω => f z.2 z.1.2) :=
    hf.stronglyMeasurable.comp_measurable (measurable_snd.prodMk measurable_fst.snd)
  exact (H.integral_kernel_prod_right' (κ:=κ)).measurable
lemma posteriorAverage_uniform_bounds {f : Ω → Position → ℝ}
    (hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |f o x|≤C) :
    ∀ D : ℝ,∃ C : ℝ,∀ a x,x∈Metric.closedBall 0 D → |posteriorAverage P obs f a x|≤C := by
  intro D
  obtain ⟨C,hC⟩ := hb D
  refine ⟨C,fun a x hx => ?_⟩
  calc
    |posteriorAverage P obs f a x| ≤ ∫ o, |f o x| ∂ProbabilityTheory.condDistrib id obs P a := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Ω, C ∂ProbabilityTheory.condDistrib id obs P a := integral_mono_of_nonneg
      (Eventually.of_forall (fun o => abs_nonneg (f o x))) (integrable_const C)
      (Eventually.of_forall (fun o => hC o x hx))
    _ = C := by simp
lemma posterior_ae {q : Ω → Prop} (ho : Measurable obs) (hq : ∀ᵐ o ∂P,q o) :
    ∀ᵐ o ∂P,∀ᵐ v ∂ProbabilityTheory.condDistrib id obs P (obs o),q v := by
  have H : ∀ᵐ v ∂(ProbabilityTheory.condDistrib id obs P ∘ₘ P.map obs),q v := by
    simpa only [ProbabilityTheory.condDistrib_comp_map ho.aemeasurable aemeasurable_id,Measure.map_id] using hq
  exact ae_of_ae_map ho.aemeasurable (Measure.ae_ae_of_ae_comp H)
lemma posteriorAverage_invariant {B C r Z L : ℝ} (hr : 0<r) (ho : Measurable obs)
    {u μ p : Ω → Position → ℝ}
    (hi : ∀ᵐ o ∂P,PropagationInvariant B C r Z L (u o) (μ o) (p o))
    (hu : Measurable (Function.uncurry u)) (hμ : Measurable (Function.uncurry μ))
    (hp : Measurable (Function.uncurry p))
    (hbu : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |u o x|≤C)
    (hbμ : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤C)
    (hbp : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |p o x|≤C) :
    ∀ᵐ o ∂P,PropagationInvariant B C r Z L (posteriorAverage P obs u (obs o))
      (posteriorAverage P obs μ (obs o)) (posteriorAverage P obs p (obs o)) := by
  filter_upwards [posterior_ae P obs ho hi] with o h
  exact PropagationInvariant.average_ae hr h hu hμ hp hbu hbμ hbp
end Posterior
end NeutralAtom
end

end
section
open MeasureTheory
noncomputable section
namespace NeutralAtom
instance observationNoise_standardBorel (n J : ℕ) : StandardBorelSpace (ObservationNoise n J) := by
  let : StandardBorelSpace (Fin 3 → ℝ) := StandardBorelSpace.pi_countable
  let : StandardBorelSpace (Fin n → Fin 3 → ℝ) := StandardBorelSpace.pi_countable
  exact StandardBorelSpace.pi_countable
instance observationSample_standardBorel (n J : ℕ) : StandardBorelSpace (ObservationSample n J) :=
  StandardBorelSpace.prod
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
lemma ae_all_position_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f g : Ω → Position → ℝ} (hf : ∀ o,Continuous (f o)) (hg : ∀ o,Continuous (g o))
    (he : ∀ x,∀ᵐ o ∂P,f o x=g o x) : ∀ᵐ o ∂P,f o=g o := by
  obtain ⟨S,hSc,hSd⟩ := TopologicalSpace.exists_countable_dense Position
  let := hSc.to_subtype
  have H : ∀ᵐ o ∂P,∀ x : S,f o x=g o x := ae_all_iff.mpr (fun x => he x)
  filter_upwards [H] with o ho
  exact Continuous.ext_on hSd (hf o) (hg o) (fun x hx => ho ⟨x,hx⟩)

theorem posteriorPacketDensity_tower {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) {c r₀ s : ℝ}
    (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (r : Fin J → ℝ) {i j : ℕ} (hij : i≤j) :
    let P := observationLaw J ν
    let μi := fun o => conditionalPacketDensity P Prod.fst (tailObservation r i) g c r₀ s (tailObservation r i o)
    ∀ᵐ o ∂P,posteriorAverage P (tailObservation r j) μi (tailObservation r j o)=
      conditionalPacketDensity P Prod.fst (tailObservation r j) g c r₀ s (tailObservation r j o) := by
  let P := observationLaw J ν
  let oi := tailObservation (n:=n) r i
  let oj := tailObservation (n:=n) r j
  let μi := fun o => conditionalPacketDensity P Prod.fst oi g c r₀ s (oi o)
  have hoi : Measurable oi := measurable_tailObservation r i
  have hoj : Measurable oj := measurable_tailObservation r j
  have hμ : Measurable (Function.uncurry μi) :=
    (measurable_conditionalPacketDensity_joint P Prod.fst oi hg hgs hc hr hs).comp (hoi.prodMap measurable_id)
  obtain ⟨A,hA,hAb⟩ := conditionalPacketDensity_bounded P Prod.fst oi hg hgs hc hr hs
  have hb : ∀ D : ℝ,∃ C : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μi o x|≤C := by
    intro D
    refine ⟨A,fun o x _ => ?_⟩
    change |conditionalPacketDensity P Prod.fst oi g c r₀ s (oi o) x|≤A
    simpa only [abs_of_nonneg (conditionalPacketDensity_nonneg P Prod.fst oi g hc hr hs (oi o) x)] using hAb (oi o) x
  apply ae_all_position_eq P
    (fun o => continuous_average_of_ball_bounds
      (fun v => conditionalPacketDensity_continuous P Prod.fst oi hg hgs hc hr hs (oi v)) hμ hb)
    (fun o => conditionalPacketDensity_continuous P Prod.fst oj hg hgs hc hr hs (oj o))
  intro x
  have hi : (fun o => μi o x)=ᵐ[P]
      P[fun o => rawPacketDensity g c r₀ s o.1 x | observationSigma r i] :=
    conditionalPacketDensity_eq_condExp P ν (observationLaw_rawProjection ν) hoi hg hgs hc hr hs x
  have hj : (fun o => conditionalPacketDensity P Prod.fst oj g c r₀ s (oj o) x)=ᵐ[P]
      P[fun o => rawPacketDensity g c r₀ s o.1 x | observationSigma r j] :=
    conditionalPacketDensity_eq_condExp P ν (observationLaw_rawProjection ν) hoj hg hgs hc hr hs x
  have hix := integrable_section_of_ball_bounds (μ:=P) hμ hb x
  have ha := ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id hoj hix
  exact ha.symm.trans ((condExp_congr_ae hi).trans
    ((condExp_condExp_of_le (observationSigma_antitone r hij) (observationSigma_le r i)).trans hj.symm))
end NeutralAtom
end

end

end OAI
