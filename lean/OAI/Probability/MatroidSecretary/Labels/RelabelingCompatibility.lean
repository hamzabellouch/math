import OAI.Probability.MatroidSecretary.Labels.LabeledTransportOneSample
import OAI.Probability.MatroidSecretary.Labels.RelabelingProphet

namespace OAI

/-! Exact agreement of two independently developed finite-label interfaces.
The bundled-rule presentation and the earlier canonical transport evaluate the
same concrete decisions, accepted prefixes, rewards, and offline benchmark. -/

namespace MatroidProphet.LabeledTransport

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {n bits : ℕ}

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem optimum_eq_canonical (M : Matroid α) (w : α → ℝ) :
    optimum M w = Relabeling.finiteOptimum M w := rfl

theorem decode_decide_eq_canonical (e : α ≃ Fin n)
    (A : MatroidProphet.OnlineRule n bits) (k : Fin n) (r : Seed bits)
    (s : α → ℝ) (h : History α k) :
    (decodeRule e A).decide k r s h = Relabeling.transportedDecision e A k r s h := rfl

theorem decode_accepted_eq_canonical (e : α ≃ Fin n)
    (A : MatroidProphet.OnlineRule n bits) (r : Seed bits) (s w : α → ℝ)
    (π : ArrivalOrder α n) (t : ℕ) :
    acceptedThrough (decodeRule e A) r s w π t =
      Relabeling.transportedAcceptedThrough e A r s w π t := rfl

theorem decode_reward_eq_canonical (e : α ≃ Fin n)
    (A : MatroidProphet.OnlineRule n bits) (r : Seed bits) (s w : α → ℝ)
    (π : ArrivalOrder α n) :
    reward (decodeRule e A) r s w π = Relabeling.transportedReward e A r s w π := rfl

end MatroidProphet.LabeledTransport

end OAI
