import OAI.Analysis.KadisonKastler.CompletelyBounded
import OAI.Analysis.KadisonKastler.CorrectionBounds

namespace OAI

/-!
# Rectangular matrix estimates for multiplication correction

The inverse and corrected-map bounds used in the UCP criterion hold at
every rectangular C⋆-matrix size. The source and target may be represented
in a third ambient C⋆-algebra.
-/

namespace KadisonKastler

variable {A B C : Type*}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] in
/-- Entrywise application respects composition on rectangular matrices. -/
theorem matrix_map_comp (F : A →ₗ[ℂ] B) (G : B →ₗ[ℂ] C) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (G.comp F) X = CStarMatrix.mapₗ G (CStarMatrix.mapₗ F X) := by
  ext i j
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- The identity linear map acts identically at every rectangular level. -/
theorem matrix_map_id {p q : ℕ} (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (LinearMap.id : A →ₗ[ℂ] A) X = X := by
  ext i j
  rfl

/-- A linear equivalence which is completely close to a complete isometry
has completely bounded inverse, with the same bound at every matrix size. -/
theorem inverse_completelyBoundedBy_of_close_isometries
    (F : A ≃ₗ[ℂ] B) (ρ : A →ₗ[ℂ] C) (ι : B →ₗ[ℂ] C) {e : ℝ}
    (he : e < 1) (hρ : CompletelyIsometric ρ) (hι : CompletelyIsometric ι)
    (hclose : CompletelyBoundedBy (ι.comp F.toLinearMap - ρ) e) :
    CompletelyBoundedBy F.symm.toLinearMap ((1 - e)⁻¹) := by
  intro p q Y
  let X := (matrixLinearEquiv F p q).symm Y
  have hFX : CStarMatrix.mapₗ F.toLinearMap X = Y :=
    (matrixLinearEquiv F p q).apply_symm_apply Y
  have hcomparison : ‖CStarMatrix.mapₗ ρ X - CStarMatrix.mapₗ ι Y‖ ≤ e * ‖X‖ := by
    have h := hclose p q X
    rw [matrix_map_sub, matrix_map_comp, hFX, norm_sub_rev] at h
    exact h
  have htriangle := norm_le_norm_sub_add (CStarMatrix.mapₗ ρ X) (CStarMatrix.mapₗ ι Y)
  rw [hρ p q X, hι p q Y] at htriangle
  have hlower : (1 - e) * ‖X‖ ≤ ‖Y‖ := by linarith
  exact (le_inv_mul_iff₀ (sub_pos.mpr he)).mpr hlower

/-- Correcting multiplication changes the represented map by at most `32e`
at every rectangular matrix size, under the explicit UCP tolerance. -/
theorem correctedMap_completelyBoundedBy_thirty_two_mul
    (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A) (ρ : A →ₗ[ℂ] C) (ι : B →ₗ[ℂ] C)
    {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000)
    (hι : CompletelyIsometric ι) (hF : CompletelyBoundedBy F.toLinearMap 1)
    (hclose : CompletelyBoundedBy (ι.comp F.toLinearMap - ρ) e)
    (hL : CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (30 * e / (1 - e))) :
    CompletelyBoundedBy (ι.comp (F.toLinearMap.comp L.symm.toLinearMap) - ρ) (32 * e) := by
  intro p q X
  have hLmatrix (Y : CStarMatrix (Fin p) (Fin q) A) :
      ‖matrixLinearEquiv L p q Y - Y‖ ≤ (30 * e / (1 - e)) * ‖Y‖ := by
    have h := hL p q Y
    rw [matrix_map_sub, matrix_map_id] at h
    exact h
  have hFmatrix (Y : CStarMatrix (Fin p) (Fin q) A) :
      ‖(CStarMatrix.mapₗ ι).comp (CStarMatrix.mapₗ F.toLinearMap) Y‖ ≤ ‖Y‖ := by
    change ‖CStarMatrix.mapₗ ι (CStarMatrix.mapₗ F.toLinearMap Y)‖ ≤ ‖Y‖
    rw [hι p q]
    simpa only [one_mul] using hF p q Y
  have hcloseMatrix (Y : CStarMatrix (Fin p) (Fin q) A) :
      ‖(CStarMatrix.mapₗ ι).comp (CStarMatrix.mapₗ F.toLinearMap) Y -
          CStarMatrix.mapₗ ρ Y‖ ≤ e * ‖Y‖ := by
    have h := hclose p q Y
    rw [matrix_map_sub, matrix_map_comp] at h
    exact h
  have hbound := norm_correctedMap_sub_le_thirty_two_mul (matrixLinearEquiv L p q)
    ((CStarMatrix.mapₗ ι).comp (CStarMatrix.mapₗ F.toLinearMap))
    (CStarMatrix.mapₗ ρ) he he₁ hLmatrix hFmatrix hcloseMatrix X
  rw [matrix_map_sub, matrix_map_comp, matrix_map_comp]
  exact hbound

end KadisonKastler

end OAI
