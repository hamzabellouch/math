import OAI.Geometry.NodalSets.Elliptic.IntrinsicAmbientExtension
import OAI.Geometry.NodalSets.Spectral.SphereRadialProjection

namespace OAI

namespace Yau.Target
open scoped RealInnerProductSpace
noncomputable section

lemma intrinsicAmbientMatrix_bounds (A : IntrinsicTensor) (a b : ℝ)
    (hlo : ∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
      a*‖v‖^2 ≤ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v))
    (hhi : ∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ b*‖v‖^2)
    (x : Base) (v : AmbientBase) :
    min a 1 * ‖v‖^2 ≤ ambientMatrixForm (intrinsicAmbientMatrix A x) v v ∧
    ambientMatrixForm (intrinsicAmbientMatrix A x) v v ≤ max b 1 * ‖v‖^2 := by
  have hl := hlo x (sphereTangentProjection x v) (sphereTangentProjection_orthogonal x v)
  have hh := hhi x (sphereTangentProjection x v) (sphereTangentProjection_orthogonal x v)
  rw [sphereTangentProjection_restriction] at hl hh
  rw [intrinsicAmbientMatrix_pairing, ← sphereTangentProjection_norm x v]
  constructor
  · calc
      _ = min a 1 * ‖sphereTangentProjection x v‖^2 + min a 1 * ⟪(x : AmbientBase),v⟫^2 := mul_add _ _ _
      _ ≤ a * ‖sphereTangentProjection x v‖^2 + 1 * ⟪(x : AmbientBase),v⟫^2 :=
        add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ b * ‖sphereTangentProjection x v‖^2 + 1 * ⟪(x : AmbientBase),v⟫^2 := by nlinarith
      _ ≤ max b 1 * ‖sphereTangentProjection x v‖^2 + max b 1 * ⟪(x : AmbientBase),v⟫^2 :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
      _ = _ := (mul_add _ _ _).symm

end
end Yau.Target

end OAI
