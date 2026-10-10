import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.InitialDatum

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
section Step
variable {Ω A : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace A]
variable {P : Measure Ω} [IsProbabilityMeasure P] {B C r R Z L l1 l2 e ξ hl hh : ℝ}
variable {μ μ' H : Ω → Position → ℝ} {bad : Ω → Prop}
lemma PropagationDatum.posteriorStep_total (d : PropagationDatum P B C r Z L μ)
    (obs : Ω → A) (ho : Measurable obs) (hR : 0<R)
    (hb : MeasurableSet {o | bad o})
    (hH : Measurable (Function.uncurry H)) (hμ : Measurable (Function.uncurry μ))
    (hbH : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |H o x|≤A)
    (hbμ : ∀ D : ℝ,∃ A : ℝ,∀ o x,x∈Metric.closedBall 0 D → |μ o x|≤A)
    (hstep : ∀ᵐ o ∂P,PropagationStepHypotheses (bad o) B C r R Z L l1 l2 e ξ hl hh
      (d.offset o) (H o) (μ o) (d.error o))
    (htower : ∀ᵐ o ∂P,posteriorAverage P obs μ (obs o)=μ' o) :
    let d' := d.posteriorStep obs ho hR hb hH hμ hbH hbμ hstep htower
    (∫ o,(∫ x,d'.error o x) ∂P)=(∫ o,(∫ x,d.error o x) ∂P)+
      (∫ o in {o | bad o},∫ x in {x : Position | r≤‖x‖ ∧ ‖x‖<R},μ o x ∂volume ∂P) := by
  dsimp only
  let q := fun o x => propagationStepError (bad o) r R ‖x‖ (μ o x) (d.error o x)
  change (∫ o,(∫ x,posteriorAverage P obs q (obs o) x) ∂P)=_
  have hq := propagationStepError_joint_measurable (r:=r) (R:=R) hb hμ d.error_measurable
  have hqb := propagationStepError_uniform_bounds (bad:=bad) (r:=r) (R:=R) hbμ d.error_bounds
  have hqs : ∀ᵐ o ∂P,∀ x,R≤‖x‖ → q o x=0 := by
    filter_upwards [d.invariant,hstep] with o hi hs
    exact (hs.next_invariant hi.error_support).error_support
  rw [posteriorAverage_total_integral (f:=q) (P:=P) obs ho hq hqb hqs]
  exact propagationStepError_total hμ hb hbμ d.error_product_integrable
end Step
end NeutralAtom
end

end

end OAI
