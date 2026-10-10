import OAI.Probability.MatroidSecretary.Labels.FiniteLabelTransport
import OAI.Probability.MatroidSecretary.Labels.RelabelingProphet

namespace OAI

/-! The two preserved arbitrary-label interfaces describe exactly the same
offline benchmark and online execution. These are definitional equalities,
not extra model-validity premises or comparisons of surrogate rewards. -/

namespace MatroidProphet.FiniteLabelAgreement

variable {E : Type*} [Fintype E] [MeasurableSpace E]
  [MeasurableSingletonClass E] {bits : ℕ}

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem optimum_eq (M : Matroid E) (w : E → ℝ) :
    Labeling.finiteOptimum M w = Relabeling.finiteOptimum M w := rfl

theorem decision_eq (A : OnlineRule (Fintype.card E) bits)
    (k : Fin (Fintype.card E)) (r : Seed bits) (s : E → ℝ)
    (h : Relabeling.LabeledHistory E k) :
    (Labeling.relabelRule A).decide k r s h =
      Relabeling.transportedDecision (Fintype.equivFin E) A k r s h := rfl

theorem acceptedThrough_eq (A : OnlineRule (Fintype.card E) bits)
    (r : Seed bits) (s v : E → ℝ) (π : Labeling.LabeledOrder E) (t : ℕ) :
    Labeling.labeledAcceptedThrough (Labeling.relabelRule A) r s v π t =
      Relabeling.transportedAcceptedThrough (Fintype.equivFin E) A r s v π t := rfl

theorem reward_eq (A : OnlineRule (Fintype.card E) bits)
    (r : Seed bits) (s v : E → ℝ) (π : Labeling.LabeledOrder E) :
    (∑ e ∈ Labeling.labeledAcceptedThrough (Labeling.relabelRule A)
        r s v π (Fintype.card E), v e) =
      Relabeling.transportedReward (Fintype.equivFin E) A r s v π := rfl

end MatroidProphet.FiniteLabelAgreement

end OAI
