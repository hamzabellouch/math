import OAI.Algebra.DepthFive.MatrixPathPairings
import OAI.Algebra.DepthFive.ImmPairingCompatibility

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

/-- Filtered four-path IMM sums are exactly the compatible internal-label sums. -/
theorem sum_four_immPaths_compatible_eq {A : Type*} [AddCommMonoid A] (d : ℕ)
    (side : Fin (d + 1) → Bool)
    (f : List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) →
      List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) →
      List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) →
      List (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) → A) :
    let paths := immPaths (d + 1) (Nat.succ_pos d)
    (∑ p : Fin paths.length, ∑ q : Fin paths.length,
      ∑ r : Fin paths.length, ∑ s : Fin paths.length,
        let P := paths.get p
        let Q := paths.get q
        let R := paths.get r
        let S := paths.get s
        if occupationShift (fun e => side e.1) P - occupationShift (fun e => side e.1) Q =
            occupationShift (fun e => side e.1) R - occupationShift (fun e => side e.1) S
        then f P Q R S else 0) =
      ∑ x : {x : Fin d → Pairings.Labels (Fin (d + 1)) // MomentPairing.Compatible 0 x},
        f (immInternalPathEdges d (fun t => (x.1 t).p))
          (immInternalPathEdges d (fun t => (x.1 t).q))
          (immInternalPathEdges d (fun t => (x.1 t).r))
          (immInternalPathEdges d (fun t => (x.1 t).s)) := by
  classical
  dsimp only
  have hp : immPaths (d + 1) (Nat.succ_pos d) =
      matrixEntryPaths (List.ofFn (id : Fin (d + 1) → Fin (d + 1))) 0 0 := by
    rw [List.ofFn_id]
    rfl
  rw [hp]
  rw [Pairings.sum_four_matrixEntryPaths_eq d (id : Fin (d + 1) → Fin (d + 1)) 0
    (fun P Q R S => if occupationShift (fun e => side e.1) P -
      occupationShift (fun e => side e.1) Q =
      occupationShift (fun e => side e.1) R - occupationShift (fun e => side e.1) S
      then f P Q R S else 0)]
  change (∑ x : Fin d → Pairings.Labels (Fin (d + 1)),
    if occupationShift (fun e => side e.1) (immInternalPathEdges d (fun t => (x t).p)) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d (fun t => (x t).q)) =
      occupationShift (fun e => side e.1) (immInternalPathEdges d (fun t => (x t).r)) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d (fun t => (x t).s))
    then f (immInternalPathEdges d (fun t => (x t).p))
      (immInternalPathEdges d (fun t => (x t).q))
      (immInternalPathEdges d (fun t => (x t).r))
      (immInternalPathEdges d (fun t => (x t).s)) else 0) = _
  simp only [immInternalPath_shift_sub_eq_iff_compatible]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

end Problem335

end

end OAI
