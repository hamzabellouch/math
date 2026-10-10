import OAI.Analysis.KadisonKastler.HaagerupCochains
import OAI.Analysis.KadisonKastler.ScalarAmplification

namespace OAI

/-! A row-column bounded bilinear map has completely bounded slices. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem bilinearProduct_diagonal_left (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (a : A)
    {p q : ℕ} (X : CStarMatrix (Fin p) (Fin q) A) :
    bilinearProduct f (diagonalAmplification a) X = CStarMatrix.mapₗ (f a) X := by
  ext i j
  simp only [bilinearProduct_apply, diagonalAmplification, diagonalStarAlgHom_apply]
  simp [apply_ite, ite_apply, map_zero]

omit [PartialOrder A] [StarOrderedRing A] in
theorem bilinearProduct_diagonal_right (f : A →ₗ[ℂ] A →ₗ[ℂ] A) (a : A)
    {p q : ℕ} (X : CStarMatrix (Fin p) (Fin q) A) :
    bilinearProduct f X (diagonalAmplification a) = CStarMatrix.mapₗ (f.flip a) X := by
  ext i j
  simp only [bilinearProduct_apply, diagonalAmplification, diagonalStarAlgHom_apply]
  simp [apply_ite, map_zero]

theorem HaagerupBound.right_slice {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (a : A) :
    CompletelyBoundedBy (f a) (c * ‖a‖) := by
  intro p q X
  rw [← bilinearProduct_diagonal_left]
  calc
    _ ≤ c * ‖diagonalAmplification (n := Fin p) a‖ * ‖X‖ := hf p p q _ X
    _ ≤ c * ‖a‖ * ‖X‖ := by
      gcongr
      exact norm_diagonalAmplification_le a

theorem HaagerupBound.left_slice {f : A →ₗ[ℂ] A →ₗ[ℂ] A} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (a : A) :
    CompletelyBoundedBy (f.flip a) (c * ‖a‖) := by
  intro p q X
  rw [← bilinearProduct_diagonal_right]
  calc
    _ ≤ c * ‖X‖ * ‖diagonalAmplification (n := Fin q) a‖ := hf p q q X _
    _ ≤ c * ‖X‖ * ‖a‖ := by
      gcongr
      exact norm_diagonalAmplification_le a
    _ = _ := by ring

end

end KadisonKastler

end OAI
