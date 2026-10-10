import OAI.Algebra.DepthFive.PathInjectivity
import OAI.Algebra.DepthFive.ImmPairingCompatibility

namespace OAI

noncomputable section
namespace Problem335

/-- The list-based layer profile of an actual internal IMM path is its vertex coordinate. -/
@[simp] theorem edgeProfile_immInternalPathEdges (d : ℕ)
    (p : Fin d → Fin (d + 1)) (t : Fin (d + 1)) :
    edgeProfile (immInternalPathEdges d p) (immInternalPathEdges_labels d p) t =
      immInternalCoordinate d p t := by
  simp only [edgeProfile, immInternalPathEdges, List.getElem_ofFn,
    immInternalCoordinate, immInternalPathVertices_castSucc, immInternalPathVertices_succ]

/-- All four list profiles agree with the layer labels defining pairing weights. -/
theorem layerLabels_eq_immPathProfiles (d : ℕ)
    (x : Fin d → Pairings.Labels (Fin (d + 1))) (t : Fin (d + 1)) :
    MomentPairing.layerLabels 0 x t =
      (⟨edgeProfile (immInternalPathEdges d (fun i => (x i).p))
          (immInternalPathEdges_labels d _) t,
        edgeProfile (immInternalPathEdges d (fun i => (x i).q))
          (immInternalPathEdges_labels d _) t,
        edgeProfile (immInternalPathEdges d (fun i => (x i).r))
          (immInternalPathEdges_labels d _) t,
        edgeProfile (immInternalPathEdges d (fun i => (x i).s))
          (immInternalPathEdges_labels d _) t⟩ :
            Pairings.Labels (Fin (d + 1) × Fin (d + 1))) := by
  simpa only [edgeProfile_immInternalPathEdges] using
    layerLabels_immInternalCoordinate d (fun i => (x i).p) (fun i => (x i).q)
      (fun i => (x i).r) (fun i => (x i).s) t

end Problem335

end

end OAI
