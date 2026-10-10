import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet
open Set Finset MeasureTheory

/-- Core and hidden prefix feasibility, measurability after masking the initial
observations, complete accepted-set nonanticipation, irrevocability, and literal
rejection of sacrificed labels. The mask depends only on the initial seed by
the type of `HiddenRule`; no weight-dependent mask is allowed. -/
def MainRuleFeasibility {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits) : Prop :=
  Feasible M A.core ∧
  (∀ k, Measurable (fun x : Seed bits × (Weights n × History n k) =>
    A.core.decide k x.1 (observed A x.1 x.2.1) x.2.2)) ∧
  (∀ (w : Weights n), (∀ e, 0 ≤ w e) →
    ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
      M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n))) ∧
  (∀ (r : Seed bits) (w w' : Weights n) (π π' : ArrivalOrder n) (t : ℕ),
    (∀ e ∈ A.mask r, w e = w' e) →
    (∀ j : Fin n, j.val < t → (π j, w (π j)) = (π' j, w' (π' j))) →
    hiddenAcceptedThrough A r w π t = hiddenAcceptedThrough A r w' π' t) ∧
  (∀ (r : Seed bits) (w : Weights n) (π : ArrivalOrder n),
    Monotone (hiddenAcceptedThrough A r w π)) ∧
  (∀ (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (t : ℕ),
    Disjoint (hiddenAcceptedThrough A r w π t) (A.mask r))

end MatroidProphet

end OAI
