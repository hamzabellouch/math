import OAI.Algebra.DepthFive.ImmSecondLocalBound
import OAI.Algebra.DepthFive.ImmPairingReindex
import OAI.Algebra.DepthFive.ImmProfileCompatibility

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

private def totalImmProfile (n : ℕ)
    (P : List (Fin n × Fin n × Fin n)) : Fin n → Fin n × Fin n :=
  if h : P.map Prod.fst = List.finRange n then edgeProfile P h else fun t => (t, t)

private theorem totalImmProfile_get (n : ℕ) (hn : 0 < n)
    (p : Fin (immPaths n hn).length) :
    totalImmProfile n ((immPaths n hn).get p) = FockLayerProfile.immProfile n hn p := by
  simp only [totalImmProfile, dite_eq_left (immPaths_labels n hn _ (List.get_mem _ p)),
    FockLayerProfile.immProfile]

private theorem totalImmProfile_internal (d : ℕ) (p : Fin d → Fin (d + 1)) :
    totalImmProfile (d + 1) (immInternalPathEdges d p) = immInternalCoordinate d p := by
  funext t
  simp only [totalImmProfile, dite_eq_left (immInternalPathEdges_labels d p),
    edgeProfile_immInternalPathEdges]

/-- The actual second trace is bounded by the compatible endpoint-path local
occupation sum, with one source sum and no remaining representation hypotheses. -/
theorem immNormalizedMatrix_second_trace_le_compatible
    (d : ℕ) (side : Fin (d + 1) → Bool) (a b : ℕ) :
    let A := immNormalizedMatrix (d + 1) side a b
    ((A.conjTranspose * A) ^ 2).trace.re ≤
      ∑ M : ImmSourceIndex (d + 1) side a b,
        ∑ x : {x : Fin d → Pairings.Labels (Fin (d + 1)) // MomentPairing.Compatible 0 x},
          ∏ t : Fin (d + 1), LocalMoments.localPolynomial (side t)
            (fun y => M.1 (t, y)) (MomentPairing.layerLabels 0 x.1 t).p
              (MomentPairing.layerLabels 0 x.1 t).q
              (MomentPairing.layerLabels 0 x.1 t).r := by
  classical
  refine (immNormalizedMatrix_second_trace_le_localPolynomial_sum
    (d + 1) (Nat.succ_pos d) side a b).trans_eq ?_
  apply Finset.sum_congr rfl
  intro M hM
  have h := sum_four_immPaths_compatible_eq d side
    (fun P Q R _ => ∏ t : Fin (d + 1), LocalMoments.localPolynomial (side t)
      (fun y => M.1 (t, y)) (totalImmProfile (d + 1) P t)
        (totalImmProfile (d + 1) Q t) (totalImmProfile (d + 1) R t))
  simp only [totalImmProfile_get, totalImmProfile_internal] at h
  convert h using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro x hx
    apply Finset.prod_congr rfl
    intro t ht
    rw [show x.1 = (fun i => ⟨(x.1 i).p, (x.1 i).q, (x.1 i).r, (x.1 i).s⟩) from rfl,
      layerLabels_immInternalCoordinate]

end Problem335

end

end OAI
