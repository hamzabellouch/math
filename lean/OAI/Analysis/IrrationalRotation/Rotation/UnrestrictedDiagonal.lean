import OAI.Analysis.IrrationalRotation.Model.UnrestrictedDiagonal
import OAI.Analysis.IrrationalRotation.Rotation.DiagonalContinuity

namespace OAI

namespace Invariant233.SequenceHilbert

variable {I : Type*}

theorem boundedDiagonal_eq (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : boundedDiagonal a = diagonal a C hC ha := by
  unfold boundedDiagonal
  split
  · rename_i h
    exact diagonal_congr a a h.choose C h.choose_spec.1 hC h.choose_spec.2 ha (fun _ => rfl)
  · rename_i h
    exact False.elim (h ⟨C, hC, ha⟩)

@[simp]
theorem boundedDiagonal_apply_of_bound (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (v : SequenceHilbert I) (i : I) :
    boundedDiagonal a v i = a i * v i := by
  rw [boundedDiagonal_eq a C hC ha, diagonal_apply]

theorem norm_boundedDiagonal_le (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : ‖boundedDiagonal a‖ ≤ C := by
  rw [boundedDiagonal_eq a C hC ha]
  exact norm_diagonal_le a C hC ha

theorem boundedDiagonal_congr {a b : I → ℂ} (h : ∀ i, a i = b i) :
    boundedDiagonal a = boundedDiagonal b := by
  exact congrArg boundedDiagonal (funext h)

end Invariant233.SequenceHilbert

end OAI
