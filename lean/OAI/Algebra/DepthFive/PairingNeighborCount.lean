import OAI.Algebra.DepthFive.PairingWeights
import OAI.Algebra.DepthFive.ScheduleWeightBridge

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.Pairings

/-- The actual path endpoints coincide with the schedule's internal ends. -/
theorem internalEndpointSet_eq_internalEnds {L : ℕ} (t : Fin (L + 1)) :
    internalEndpointSet t = BalancedSchedule.internalEnds t := by
  ext v
  simp [internalEndpointSet, BalancedSchedule.internalEnds, Fin.ext_iff]

/-- Boolean word form of the normal-endpoint exponent in the weighted
relaxed-path count, using the canonical schedule coincidence set. -/
theorem normalEndpointCount_eq_nnInternalEnds_card {L : ℕ}
    (w : Fin (L + 1) → Bool) (t : Fin (L + 1)) :
    normalEndpointCount (fun i => boolKindEquiv (w i)) (internalEndpointSet t) =
      (BalancedSchedule.nnInternalEnds w t).card := by
  have hbool (b : Bool) : boolKindEquiv b = .normal ↔ b = false := by
    cases b <;> simp
  unfold normalEndpointCount BalancedSchedule.nnInternalEnds
  rw [internalEndpointSet_eq_internalEnds]
  congr 1
  apply Finset.filter_congr
  intro v hv
  simp only [hbool]
  rfl

/-- At a normal layer the relaxed-path exponent is precisely the canonical
graph-word false-neighbor count. -/
theorem normalEndpointCount_eq_falseNeighbors_card {L : ℕ}
    (w : Fin (L + 1) → Bool) (t : Fin (L + 1)) (ht : w t = false) :
    normalEndpointCount (fun i => boolKindEquiv (w i)) (internalEndpointSet t) =
      (IsolatedWeight.falseNeighbors BalancedSchedule.adjacent w t).card := by
  rw [normalEndpointCount_eq_nnInternalEnds_card]
  exact (BalancedSchedule.falseNeighbors_card_eq_nnInternalEnds_card w t ht).symm

/-- The complete word correction expressed in the exponents supplied by the
actual relaxed-path averaging theorem. -/
theorem correction_eq_normalEndpointCount_product {L : ℕ}
    (V : Finset (Fin (L + 1))) (w : Fin (L + 1) → Bool) (A x : ℝ) :
    IsolatedWeight.correction V BalancedSchedule.adjacent A x w =
      ∏ t ∈ V.filter (fun t => w t = false),
        (1 + A * x ^ normalEndpointCount (fun i => boolKindEquiv (w i))
          (internalEndpointSet t)) := by
  rw [BalancedSchedule.correction_eq_nnInternalEnds_product]
  simp_rw [normalEndpointCount_eq_nnInternalEnds_card]

end Problem335.Pairings

end

end OAI
