import OAI.Analysis.KadisonKastler.OperatorCochainStar

namespace OAI

/-! # The quadratic remainder of the full-operator cochain contraction -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance cochainResidualOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance cochainResidualOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] in
theorem mul_cochainColumn (φ : H →L[ℂ] ℂ) (a : H →L[ℂ] H) (y : H) :
    a * cochainColumn φ y = cochainColumn φ (a y) := by
  ext z
  simp

omit [CompleteSpace H] in
theorem cochainColumnMatrix_product (φ : H →L[ℂ] ℂ) {p r q : ℕ}
    (j : Fin q) (Y : CStarMatrix (Fin p) (Fin r) (H →L[ℂ] H))
    (y : Generator.FiniteHilbert (Fin r) H) :
    Y * cochainColumnMatrix φ j y =
      cochainColumnMatrix φ j (rectangularHilbertMatrix Y y) := by
  ext i k
  by_cases hk : k = j
  · subst k
    simp [CStarMatrix.mul_apply, mul_cochainColumn, rectangularHilbertMatrix_apply, map_sum]
  · simp [CStarMatrix.mul_apply, hk]

omit [CompleteSpace H] in
theorem rectangularHilbertMatrix_add {p q : ℕ}
    (X Y : CStarMatrix (Fin p) (Fin q) (H →L[ℂ] H)) :
    rectangularHilbertMatrix (X + Y) = rectangularHilbertMatrix X + rectangularHilbertMatrix Y := by
  ext z i
  simp [rectangularHilbertMatrix_apply, Finset.sum_add_distrib]

omit [CompleteSpace H] in
theorem rectangularHilbertMatrix_sub {p q : ℕ}
    (X Y : CStarMatrix (Fin p) (Fin q) (H →L[ℂ] H)) :
    rectangularHilbertMatrix (X - Y) = rectangularHilbertMatrix X - rectangularHilbertMatrix Y := by
  ext z i
  simp [rectangularHilbertMatrix_apply, Finset.sum_sub_distrib]

/-- Evaluating the differential on the last rank-one column is exactly the
negative residual of the contracted cochain. -/
theorem operatorCochainContraction_residual_identity
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (φ : H →L[ℂ] ℂ) (ξ : H) (hφ : φ ξ = 1)
    {p r q t : ℕ} (j : Fin t)
    (X : CStarMatrix (Fin p) (Fin r) (H →L[ℂ] H))
    (Y : CStarMatrix (Fin r) (Fin q) (H →L[ℂ] H))
    (y : Generator.FiniteHilbert (Fin q) H) :
    rectangularHilbertMatrix
      (bilinearProduct (f - linearCoboundary (operatorCochainContraction hf hc φ ξ).toLinearMap) X Y) y =
      -rectangularHilbertMatrix (matrixBilinearDifferential f X Y (cochainColumnMatrix φ j y))
        (Generator.tupleSingle j ξ) := by
  have hK : rectangularHilbertMatrix (cochainColumnMatrix φ j y)
      (Generator.tupleSingle j ξ) = y := by
    rw [hilbertMatrix_cochainColumnMatrix]
    simp [Generator.tupleSingle_apply, hφ]
  have hdiff : rectangularHilbertMatrix
      (matrixBilinearDifferential f X Y (cochainColumnMatrix φ j y))
      (Generator.tupleSingle j ξ) =
      rectangularHilbertMatrix X
          (rectangularHilbertMatrix (CStarMatrix.mapₗ (operatorCochainContraction hf hc φ ξ).toLinearMap Y) y) -
        rectangularHilbertMatrix
          (CStarMatrix.mapₗ (operatorCochainContraction hf hc φ ξ).toLinearMap (X * Y)) y +
        rectangularHilbertMatrix (CStarMatrix.mapₗ (operatorCochainContraction hf hc φ ξ).toLinearMap X)
          (rectangularHilbertMatrix Y y) -
        rectangularHilbertMatrix (bilinearProduct f X Y) y := by
    simp only [matrixBilinearDifferential, rectangularHilbertMatrix_sub,
      rectangularHilbertMatrix_add, sub_apply, add_apply,
      rectangularHilbertMatrix_mul, ContinuousLinearMap.comp_apply]
    rw [hK, cochainColumnMatrix_product]
    rw [← operatorCochainContraction_matrix_action hf hc φ ξ j,
      ← operatorCochainContraction_matrix_action hf hc φ ξ j,
      ← operatorCochainContraction_matrix_action hf hc φ ξ j]
  rw [hdiff, bilinearProduct_sub, bilinearProduct_linearCoboundary,
    rectangularHilbertMatrix_sub, rectangularHilbertMatrix_add,
    rectangularHilbertMatrix_sub, rectangularHilbertMatrix_mul, rectangularHilbertMatrix_mul]
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply]
  abel

/-- The contracted cochain leaves at most the exact quadratic differential
bound. The estimate holds on every rectangular matrix pair. -/
theorem operatorCochainContraction_residual_bound
    (m : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H))
    (hm : ∀ x y z, m (m x y) z = m x (m y z)) {c : ℝ} (hc : 0 ≤ c)
    (hf : HaagerupBound (m - LinearMap.mul ℂ (H →L[ℂ] H)) c)
    (φ : H →L[ℂ] ℂ) (ξ : H) (hφ : φ ξ = 1) :
    HaagerupBound (m - LinearMap.mul ℂ (H →L[ℂ] H) -
      linearCoboundary (operatorCochainContraction hf hc φ ξ).toLinearMap)
      (2 * c ^ 2 * ‖φ‖ * ‖ξ‖) := by
  intro p r q X Y
  rw [← norm_rectangularHilbertMatrix]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  let j : Fin 1 := 0
  rw [operatorCochainContraction_residual_identity hf hc φ ξ hφ j, norm_neg]
  calc
    _ ≤ ‖matrixBilinearDifferential (m - LinearMap.mul ℂ (H →L[ℂ] H)) X Y
          (cochainColumnMatrix φ j y)‖ * ‖ξ‖ := by
      simpa only [norm_rectangularHilbertMatrix, norm_tupleSingle] using
        (rectangularHilbertMatrix
          (matrixBilinearDifferential (m - LinearMap.mul ℂ (H →L[ℂ] H)) X Y
            (cochainColumnMatrix φ j y))).le_opNorm (Generator.tupleSingle j ξ)
    _ ≤ (2 * c ^ 2 * ‖X‖ * ‖Y‖ * (‖φ‖ * ‖y‖)) * ‖ξ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg ξ)
      exact (matrixBilinearDifferential_defect_bound m hm hc hf X Y _).trans
        (mul_le_mul_of_nonneg_left (norm_cochainColumnMatrix_le φ j y) (by positivity))
    _ = _ := by ring

end

end KadisonKastler

end OAI
