import OAI.Algebra.DepthFive.RelaxedWeightBound
import OAI.Algebra.DepthFive.PairingNeighborCount

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.MomentPairing
open Pairings

/-- The averaged pairing summand is exactly the canonical Boolean-word weight. -/
theorem relaxedWordWeight_eq_isolatedWeight {L : ℕ}
    (isV w : Fin (L + 1) → Bool) (N α β : ℝ) :
    relaxedWordWeight isV N α β (fun i => boolKindEquiv (w i)) =
      IsolatedWeight.weight (BalancedSchedule.internalEdges (L + 1))
        (Finset.univ.filter (fun i => isV i = true))
        BalancedSchedule.adjacent α⁻¹ β N⁻¹ w := by
  classical
  have hn (b : Bool) : boolKindEquiv b = Kind.normal ↔ b = false := by
    cases b <;> simp
  have hd (b : Bool) : boolKindEquiv b = Kind.diagonal ↔ b = true := by
    cases b <;> simp
  have hs : adjacentSwitches (fun i => boolKindEquiv (w i)) =
      SwitchRestoration.switchCount (BalancedSchedule.internalEdges (L + 1)) w := by
    rw [BalancedSchedule.internalEdges_eq_pathEdges, SwitchRestoration.switchCount_pathEdges]
    simp only [adjacentSwitches, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    simp only [show (boolKindEquiv (w i.castSucc) ≠ boolKindEquiv (w i.succ)) ↔
      w i.castSucc ≠ w i.succ from not_congr boolKindEquiv.injective.eq_iff]
  have hv : diagonalVCount isV (fun i => boolKindEquiv (w i)) =
      ((Finset.univ.filter (fun i => isV i = true)).filter (fun i => w i = true)).card := by
    simp only [diagonalVCount, hd, Finset.filter_filter]
  have hu : diagonalUCount isV (fun i => boolKindEquiv (w i)) =
      ((Finset.univ \ Finset.univ.filter (fun i => isV i = true)).filter
        (fun i => w i = true)).card := by
    unfold diagonalUCount
    congr 1
    ext i
    simp only [ Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and, hd]
    cases isV i <;> simp
  have hnV : normalVLayers isV (fun i => boolKindEquiv (w i)) =
      (Finset.univ.filter (fun i => isV i = true)).filter (fun i => w i = false) := by
    ext i
    simp [normalVLayers, hn]
  unfold relaxedWordWeight IsolatedWeight.weight
  rw [hs, hv, hu, correction_eq_normalEndpointCount_product]
  congr 1
  simpa only [hnV] using
    (Finset.prod_coe_sort (normalVLayers isV (fun i => boolKindEquiv (w i)))
      (fun t : Fin (L + 1) => 1 + α⁻¹ * N⁻¹ ^
        normalEndpointCount (fun i => boolKindEquiv (w i)) (internalEndpointSet t)))

/-- Reindexing all pairing words through the canonical Boolean equivalence. -/
theorem sum_relaxedWordWeight_eq_isolatedWeight {L : ℕ}
    (isV : Fin (L + 1) → Bool) (N α β : ℝ) :
    (∑ τ : Fin (L + 1) → Kind, relaxedWordWeight isV N α β τ) =
      ∑ w : Fin (L + 1) → Bool,
        IsolatedWeight.weight (BalancedSchedule.internalEdges (L + 1))
          (Finset.univ.filter (fun i => isV i = true))
          BalancedSchedule.adjacent α⁻¹ β N⁻¹ w := by
  let e : (Fin (L + 1) → Bool) ≃ (Fin (L + 1) → Kind) :=
    Equiv.piCongrRight (fun _ => boolKindEquiv)
  symm
  apply Fintype.sum_equiv e
  intro w
  exact (relaxedWordWeight_eq_isolatedWeight isV w N α β).symm

end Problem335.MomentPairing

end

end OAI
