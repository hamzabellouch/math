import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeDiscardedSum
import OAI.Analysis.LipschitzHilbert.Estimates.RetainedAmplitudeMatrix

namespace OAI

/-! All finite collections of actual amplitude levels split into the
retained logarithmic cost and the two exponentially small mass tails. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

def amplitudeTailCost (Q L : ℝ) : ℝ :=
  (8+2*(2/(1-(Real.sqrt 2)⁻¹)))*Q*Real.exp (-L/8)

theorem amplitudeLevel_all_weights (mu : Measure X) (f : X → E)
    (hf : MemLp f 2 mu) (hm : Measurable (fun x => ‖f x‖))
    (hf1 : Integrable (fun x => ‖f x‖) mu) (I : Finset ℤ) (M0 Q C0 L : ℝ)
    (hM0 : 0<M0) (hQ : 0≤Q) (hL : 0≤L) (hinfty : ∀ x, ‖f x‖≤Q)
    (hL1 : (∫ x, ‖f x‖ ∂mu)≤Q*M0) (hL2 : (∫ x, ‖f x‖^2 ∂mu)≤C0*M0)
    (hpos : ∀ i∈I, 0<mu.real (amplitudeLevel f i)) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mu.real (amplitudeLevel f i)/M0))≤
      retainedAmplitudeCost C0 (L/4)+amplitudeTailCost Q L := by
  classical
  let P := fun i : ℤ => |Real.log (mu.real (amplitudeLevel f i)/M0)|≤L/4
  have hret := amplitudeLevel_retained_sum mu f hf hm (I.filter P) M0 C0 (L/4)
    hM0 (by positivity) hL2 (fun i hi => hpos i (Finset.mem_filter.mp hi).1)
    (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hdrop := amplitudeLevel_discarded_sum mu f hf hm hf1 (I.filter (fun i => ¬P i)) M0 Q L
    hM0 hQ hinfty hL1 (fun i hi => hpos i (Finset.mem_filter.mp hi).1)
    (fun _ hi => lt_of_not_ge (Finset.mem_filter.mp hi).2)
  rw [←Finset.sum_filter_add_sum_filter_not I P]
  exact add_le_add hret hdrop

end LipschitzHilbert

end

end OAI
