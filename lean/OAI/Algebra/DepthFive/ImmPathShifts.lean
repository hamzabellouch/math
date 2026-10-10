import OAI.Algebra.DepthFive.ImmOperatorPaths
import OAI.Algebra.DepthFive.FockPaths
import OAI.Algebra.DepthFive.PathShifts

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The signed creation/annihilation shift of the actual IMM edge list is
exactly the layered vertex-path shift. -/
theorem occupationShift_immInternalPathEdges (d : ℕ) (side : Fin (d + 1) → Bool)
    (p : Fin d → Fin (d + 1)) :
    occupationShift (fun e => side e.1) (immInternalPathEdges d p) =
      pathShift (fun t => if side t then (-1 : ℤ) else 1)
        (immInternalPathVertices d p) := by
  simp only [occupationShift, immInternalPathEdges, List.map_ofFn,
    List.sum_ofFn, Function.comp_def, pathShift,
    immInternalPathVertices_castSucc, immInternalPathVertices_succ]

/-- Different IMM paths have different signed occupation shifts. -/
theorem occupationShift_immInternalPathEdges_injective (d : ℕ)
    (side : Fin (d + 1) → Bool) :
    Function.Injective (fun p : Fin d → Fin (d + 1) =>
      occupationShift (fun e => side e.1) (immInternalPathEdges d p)) := by
  intro p q hpq
  dsimp only at hpq
  rw [occupationShift_immInternalPathEdges, occupationShift_immInternalPathEdges] at hpq
  apply immInternalPathVertices_injective d
  apply pathShift_injective (Nat.succ_pos d) _ (fun t => ?_) hpq
  cases side t <;> norm_num

/-- Nonzero normalized IMM path actions cannot collide at a natural occupation. -/
theorem immInternalPath_target_injective_of_amplitudes_ne_zero (d : ℕ)
    (side : Fin (d + 1) → Bool)
    (M : (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) →₀ ℕ)
    (p q : Fin d → Fin (d + 1))
    (hp : ((immInternalPathEdges d p).map
      (occupationAmplitude (fun e => side e.1) M)).prod ≠ 0)
    (hq : ((immInternalPathEdges d q).map
      (occupationAmplitude (fun e => side e.1) M)).prod ≠ 0)
    (heq : pathOccupation (fun e => side e.1) (immInternalPathEdges d p) M =
      pathOccupation (fun e => side e.1) (immInternalPathEdges d q) M) : p = q := by
  apply occupationShift_immInternalPathEdges_injective d side
  apply add_left_cancel (a := signedOccupation M)
  rw [← signedOccupation_path_of_amplitude_ne_zero _ _
      (immInternalPathEdges_nodup d p) M hp,
    ← signedOccupation_path_of_amplitude_ne_zero _ _
      (immInternalPathEdges_nodup d q) M hq, heq]

/-- The collision-zero hypothesis of the first-trace expansion for genuine IMM paths. -/
theorem immInternalPath_collision_zero (d : ℕ) (side : Fin (d + 1) → Bool)
    (M : (Fin (d + 1) × Fin (d + 1) × Fin (d + 1)) →₀ ℕ)
    (p q : Fin d → Fin (d + 1)) (hpq : p ≠ q)
    (heq : pathOccupation (fun e => side e.1) (immInternalPathEdges d p) M =
      pathOccupation (fun e => side e.1) (immInternalPathEdges d q) M) :
    ((immInternalPathEdges d p).map (occupationAmplitude (fun e => side e.1) M)).prod *
      ((immInternalPathEdges d q).map (occupationAmplitude (fun e => side e.1) M)).prod = 0 := by
  by_cases hp : ((immInternalPathEdges d p).map
      (occupationAmplitude (fun e => side e.1) M)).prod = 0
  · simp [hp]
  by_cases hq : ((immInternalPathEdges d q).map
      (occupationAmplitude (fun e => side e.1) M)).prod = 0
  · simp [hq]
  exact (hpq (immInternalPath_target_injective_of_amplitudes_ne_zero d side M p q hp hq heq)).elim

end Problem335

end

end OAI
