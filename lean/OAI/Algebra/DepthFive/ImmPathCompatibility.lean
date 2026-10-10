import OAI.Algebra.DepthFive.ImmPathShifts
import OAI.Algebra.DepthFive.Pairings

namespace OAI

noncomputable section

namespace Problem335

/-- The coordinate in one layer of a genuine endpoint-fixed internal path. -/
def immInternalCoordinate (d : ℕ) (p : Fin d → Fin (d + 1))
    (t : Fin (d + 1)) : Fin (d + 1) × Fin (d + 1) :=
  (immInternalPathVertices d p t.castSucc, immInternalPathVertices d p t.succ)

/-- Four genuine IMM path shifts are compatible exactly when their coordinate
vectors are compatible separately in each layer. -/
theorem immInternalPath_shift_sub_eq_iff (d : ℕ) (side : Fin (d + 1) → Bool)
    (p q r s : Fin d → Fin (d + 1)) :
    occupationShift (fun e => side e.1) (immInternalPathEdges d p) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d q) =
      occupationShift (fun e => side e.1) (immInternalPathEdges d r) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d s) ↔
      ∀ t, Finsupp.single (immInternalCoordinate d p t) (1 : ℤ) -
          Finsupp.single (immInternalCoordinate d q t) 1 =
        Finsupp.single (immInternalCoordinate d r t) 1 -
          Finsupp.single (immInternalCoordinate d s t) 1 := by
  simp only [occupationShift_immInternalPathEdges]
  exact pathShift_sub_eq_iff _ (fun t => by cases side t <;> norm_num) _ _ _ _

/-- The exact normal/diagonal pairing alternative for genuine IMM paths.
The all-equal case is assigned only to the normal alternative. -/
theorem immInternalPath_shift_sub_eq_iff_pairings (d : ℕ)
    (side : Fin (d + 1) → Bool) (p q r s : Fin d → Fin (d + 1)) :
    occupationShift (fun e => side e.1) (immInternalPathEdges d p) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d q) =
      occupationShift (fun e => side e.1) (immInternalPathEdges d r) -
        occupationShift (fun e => side e.1) (immInternalPathEdges d s) ↔
      ∀ t,
        (immInternalCoordinate d p t = immInternalCoordinate d q t ∧
          immInternalCoordinate d r t = immInternalCoordinate d s t) ∨
        (immInternalCoordinate d p t = immInternalCoordinate d r t ∧
          immInternalCoordinate d q t = immInternalCoordinate d s t ∧
          immInternalCoordinate d p t ≠ immInternalCoordinate d q t) := by
  rw [immInternalPath_shift_sub_eq_iff]
  exact forall_congr' fun t => Pairings.coordinate_difference_eq_iff_exclusive _ _ _ _

end Problem335

end

end OAI
