import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorDensityContinuity

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure PropagationDatum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B C r Z L : ℝ) (μ : Ω → Position → ℝ) where
  offset : Ω → Position → ℝ
  error : Ω → Position → ℝ
  offset_measurable : Measurable (Function.uncurry offset)
  error_measurable : Measurable (Function.uncurry error)
  offset_bounds : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |offset o x|≤A
  error_bounds : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |error o x|≤A
  invariant : ∀ᵐ o ∂P,PropagationInvariant B C r Z L (offset o) (μ o) (error o)

section Step
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable {P : Measure Ω} [IsProbabilityMeasure P] {B C r R Z L l1 l2 e ξ hl hh : ℝ}
variable {μ μ' H : Ω → Position → ℝ} {bad : Ω → Prop}

def PropagationDatum.posteriorStep (d : PropagationDatum P B C r Z L μ)
    (obs : Ω → A) (ho : Measurable obs) (hR : 0<R)
    (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) (hμ : Measurable (Function.uncurry μ))
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A)
    (hbμ : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤A)
    (hstep : ∀ᵐ o ∂P,PropagationStepHypotheses (bad o) B C r R Z L l1 l2 e ξ hl hh
      (d.offset o) (H o) (μ o) (d.error o))
    (htower : ∀ᵐ o ∂P,posteriorAverage P obs μ (obs o)=μ' o) :
    PropagationDatum P B C R Z L μ' := by
  let v := fun o => propagationNextOffset (bad o) B R Z L l1 l2 (d.offset o) (H o)
  let q := fun o x => propagationStepError (bad o) r R ‖x‖ (μ o x) (d.error o x)
  have hv := propagationNextOffset_joint_measurable (B:=B) (Z:=Z) (L:=L) (l1:=l1) (l2:=l2)
    hR hb d.offset_measurable hH
  have hq := propagationStepError_joint_measurable (r:=r) (R:=R) hb hμ d.error_measurable
  have hvb := propagationNextOffset_uniform_bounds (bad:=bad) (B:=B) (Z:=Z) (L:=L) (l1:=l1) (l2:=l2)
    hR d.offset_bounds hbH
  have hqb := propagationStepError_uniform_bounds (bad:=bad) (r:=r) (R:=R) hbμ d.error_bounds
  refine ⟨fun o => posteriorAverage P obs v (obs o),fun o => posteriorAverage P obs q (obs o),
    (posteriorAverage_joint_measurable P obs (f:=v) hv).comp (ho.prodMap measurable_id),
    (posteriorAverage_joint_measurable P obs (f:=q) hq).comp (ho.prodMap measurable_id),?_,?_,?_⟩
  · intro D
    obtain ⟨K,hK⟩ := posteriorAverage_uniform_bounds P obs hvb D
    exact ⟨K,fun o => hK (obs o)⟩
  · intro D
    obtain ⟨K,hK⟩ := posteriorAverage_uniform_bounds P obs hqb D
    exact ⟨K,fun o => hK (obs o)⟩
  · have hi : ∀ᵐ o ∂P,PropagationInvariant B C R Z L (v o) (μ o) (q o) := by
      filter_upwards [d.invariant,hstep] with o hoi hos
      exact hos.next_invariant hoi.error_support
    have Havg := posteriorAverage_invariant P obs hR ho hi hv hμ hq hvb hbμ hqb
    filter_upwards [Havg,htower] with o hi ht
    simpa only [ht] using hi
end Step
end NeutralAtom
end

end

end OAI
