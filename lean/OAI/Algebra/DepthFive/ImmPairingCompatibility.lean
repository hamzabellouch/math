import OAI.Algebra.DepthFive.ImmPathCompatibility
import OAI.Algebra.DepthFive.SecondMomentPairing

namespace OAI

noncomputable section

namespace Problem335

/-- Closing the four internal IMM paths gives the canonical endpoint-fixed labels. -/
theorem closePaths_immInternalPathVertices (d : ℕ)
    (p q r s : Fin d → Fin (d + 1)) (t : Fin (d + 2)) :
    Pairings.closePaths 0 (fun i => ⟨p i, q i, r i, s i⟩) t =
      (⟨immInternalPathVertices d p t, immInternalPathVertices d q t,
        immInternalPathVertices d r t, immInternalPathVertices d s t⟩ :
          Pairings.Labels (Fin (d + 1))) := by
  refine Fin.cases ?_ (fun i => ?_) t
  · rfl
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.succ_last, Pairings.closePaths_last, immInternalPathVertices_end]
      rfl
    · simp [Pairings.closePaths, immInternalPathVertices]

/-- Layer labels used in the relaxed pairing sum are the actual four IMM coordinates. -/
theorem layerLabels_immInternalCoordinate (d : ℕ)
    (p q r s : Fin d → Fin (d + 1)) (t : Fin (d + 1)) :
    MomentPairing.layerLabels 0 (fun i => ⟨p i, q i, r i, s i⟩) t =
      (⟨immInternalCoordinate d p t, immInternalCoordinate d q t,
        immInternalCoordinate d r t, immInternalCoordinate d s t⟩ :
          Pairings.Labels (Fin (d + 1) × Fin (d + 1))) := by
  simp only [MomentPairing.layerLabels, closePaths_immInternalPathVertices]
  rfl

/-- The actual four-path shift constraint is exactly the compatibility predicate
used by the weighted exact-to-relaxed pairing inequality. -/
theorem immInternalPath_shift_sub_eq_iff_compatible (d : ℕ)
    (side : Fin (d + 1) → Bool) (p q r s : Fin d → Fin (d + 1)) :
    occupationShift (fun e => side e.1) (immInternalPathEdges d p) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d q) =
      occupationShift (fun e => side e.1) (immInternalPathEdges d r) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d s) ↔
      MomentPairing.Compatible 0 (fun i => ⟨p i, q i, r i, s i⟩) := by
  rw [immInternalPath_shift_sub_eq_iff]
  simp only [MomentPairing.Compatible, layerLabels_immInternalCoordinate]

end Problem335

end

end OAI
