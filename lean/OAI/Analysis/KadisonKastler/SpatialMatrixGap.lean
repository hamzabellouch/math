import OAI.Analysis.KadisonKastler.SpatialMatrixDensity

namespace OAI

/-! # Spatial-product gap from matrix unit-ball approximation

The hypothesis is complete matrix proximity. Ordinary proximity is not
asserted to remain unchanged under amplification.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial K]
variable {s : ℕ → ℕ} (E : ∀ n, MatrixUnitSystem (Fin (s n)) (K →L[ℂ] K))

private theorem spatialMatrix_test_approx
    {M N : VonNeumannAlgebra H} {γ : ℝ} (h : MatrixNearInclusion M N γ)
    (hs : ∀ n, 0 < s n) (hE : Monotone (fun n => (E n).algebra))
    (a : {a : ↥(⨆ n, spatialMatrixAlgebra M (E n)) // ‖a‖ ≤ 1}) :
    ∃ b ∈ unitBall (spatialProductAlgebra N
        (generatedVonNeumannAlgebra (⨆ n, (E n).algebra))),
      ‖(a.val : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) - b‖ ≤ γ := by
  obtain ⟨n, X, hX, hXn, hXa⟩ :=
    exists_spatialMatrix_of_stage_union M E hs hE a.val.property a.property
  let : NeZero (s n) := ⟨(hs n).ne'⟩
  obtain ⟨Y, hY, hYn, hXY⟩ := h.spatialMatrix_approx (E n) X hX hXn
  refine ⟨spatialMatrixHom (E n) Y, ⟨?_, ?_⟩, ?_⟩
  · apply spatialMatrixHom_mem N _ (E n) _ Y hY
    intro i j
    exact subset_generatedVonNeumannAlgebra _
      ((le_iSup (fun n => (E n).algebra) n) ((E n).entry_mem i j))
  · simpa only [norm_spatialMatrixHom] using hYn
  · rwa [hXa] at hXY

/-- Complete one-sided approximation extends to the spatial product with
an increasing matrix-generated von Neumann algebra. -/
theorem MatrixNearInclusion.spatialProduct_approx
    (hK : PublishedKaplanskyDensity.{u})
    {M N : VonNeumannAlgebra H} {γ : ℝ} (hγ : 0 ≤ γ)
    (h : MatrixNearInclusion M N γ)
    (hs : ∀ n, 0 < s n) (hE : Monotone (fun n => (E n).algebra))
    (a : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (ha : a ∈ unitBall (spatialProductAlgebra M
      (generatedVonNeumannAlgebra (⨆ n, (E n).algebra)))) :
    ∃ b ∈ unitBall (spatialProductAlgebra N
        (generatedVonNeumannAlgebra (⨆ n, (E n).algebra))), ‖a - b‖ ≤ γ := by
  exact exists_unitBall_approx_of_weakly_dense_tests _
    (spatialMatrix_union_weakUnitBallDense M E hK hE) hγ
    (spatialMatrix_test_approx E h hs hE) a ha

/-- Two-sided complete matrix proximity controls the ordinary gap of the
actual spatial products, with no loss in the constant. -/
theorem kkDistance_spatialProduct_le_of_matrixNearInclusion
    (hK : PublishedKaplanskyDensity.{u})
    (M N : VonNeumannAlgebra H) {γ : ℝ} (hγ : 0 ≤ γ)
    (hMN : MatrixNearInclusion M N γ) (hNM : MatrixNearInclusion N M γ)
    (hs : ∀ n, 0 < s n) (hE : Monotone (fun n => (E n).algebra)) :
    kkDistance (spatialProductAlgebra M
        (generatedVonNeumannAlgebra (⨆ n, (E n).algebra)))
      (spatialProductAlgebra N
        (generatedVonNeumannAlgebra (⨆ n, (E n).algebra))) ≤ γ := by
  exact kkDistance_le_of_weakly_dense_tests _ _ _ _
    (spatialMatrix_union_weakUnitBallDense M E hK hE)
    (spatialMatrix_union_weakUnitBallDense N E hK hE) hγ
    (spatialMatrix_test_approx E hMN hs hE)
    (spatialMatrix_test_approx E hNM hs hE)

end

end KadisonKastler

end OAI
