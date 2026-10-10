import OAI.Analysis.IrrationalRotation.Model.CircleTruncationEvent
import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingAttenuation

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleCoupling

lemma truncationEvent_subset_tagEvent (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) :
    truncationEvent p j hr r ⊆ tagEvent p j := fun _ h => h.2.1

lemma measurableSet_truncationEvent {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ} (hrm : Measurable r) :
    MeasurableSet (truncationEvent p j hr r) := by
  have hx (i : ℕ) : Measurable (fun ω : Sample => (ω i).2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_pi_apply i))
  have hy (i : ℕ) : Measurable (fun ω : Sample => (ω i).2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i))
  simp only [truncationEvent, Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter ?_ ((measurableSet_tagEvent p j).inter
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)))
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (measurableSet_lt (hx i) measurable_const).inter
        (measurableSet_lt measurable_const (hy i))
  · exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        (measurableSet_lt (hx i) measurable_const).inter
          (measurableSet_lt measurable_const (hy i))
  · exact measurableSet_le measurable_const (hrm.comp (measurable_point hp hr false))
  · exact measurableSet_le measurable_const
      (measurable_const.sub (hrm.comp (measurable_point hp hr true)))

end Invariant233.CircleCoupling

end

end OAI
