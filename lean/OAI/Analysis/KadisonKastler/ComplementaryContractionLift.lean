import OAI.Analysis.KadisonKastler.IsometryComplement

namespace OAI

/-! # A contractive lift perpendicular to a prescribed isometry

This is the geometric completion step: the unused norm in one coordinate
supports a new column perpendicular to the already prescribed column.
-/

namespace KadisonKastler

noncomputable section

variable {E F G K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_complementary_contraction_lift
    (V : E →ₗᵢ[ℂ] K) (J : F →ₗᵢ[ℂ] K) (B : G →L[ℂ] F)
    (h : ∀ y, ‖V.toContinuousLinearMap.adjoint (J y)‖ ^ 2 +
      ‖B.adjoint y‖ ^ 2 ≤ ‖y‖ ^ 2) :
    ∃ Y : G →L[ℂ] K, ‖Y‖ ≤ 1 ∧
      J.toContinuousLinearMap.adjoint.comp Y = B ∧
      V.toContinuousLinearMap.adjoint.comp Y = 0 := by
  let Q := isometryComplement V
  let W := Q.comp J.toContinuousLinearMap
  have hW (y : F) : ‖W y‖ ^ 2 =
      ‖y‖ ^ 2 - ‖V.toContinuousLinearMap.adjoint (J y)‖ ^ 2 := by
    change ‖isometryComplement V (J y)‖ ^ 2 = _
    rw [norm_isometryComplement_sq, J.norm_map]
  have hdom (y : F) : ‖B.adjoint y‖ ≤ ‖W y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hW]
    linarith [h y]
  obtain ⟨L, hL, hLW⟩ := exists_contraction_factor W B.adjoint hdom
  let Y := Q.comp L.adjoint
  refine ⟨Y, ?_, ?_, ?_⟩
  · have hLa : ‖L.adjoint‖ ≤ 1 := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using hL
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (isometryComplement_norm_le V) hLa (norm_nonneg L.adjoint) zero_le_one).trans_eq
        (mul_one 1))
  · have hadj := congrArg ContinuousLinearMap.adjoint hLW
    simpa only [W, ContinuousLinearMap.adjoint_comp, Q, isometryComplement_adjoint,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc] using hadj
  · apply ContinuousLinearMap.ext
    intro z
    exact adjoint_isometry_complement V (L.adjoint z)

end

end KadisonKastler

end OAI
