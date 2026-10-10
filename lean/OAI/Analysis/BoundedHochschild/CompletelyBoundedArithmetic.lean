import OAI.Analysis.BoundedHochschild.MatrixRightAveraging

namespace OAI

/-! Finite linear combinations and left multiplication in the input and
output preserve the complete bounds needed to combine finitely many maps. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma completelyBounded_add {T U : M →L[ℂ] M} {C D : ℝ}
    (hT : CompletelyBoundedEstimate T C) (hU : CompletelyBoundedEstimate U D) :
    CompletelyBoundedEstimate (T + U) (C + D) := by
  refine ⟨add_nonneg hT.1 hU.1, fun n A => ?_⟩
  have he : A.map (T + U) = A.map T + A.map U := by ext i j; rfl
  rw [he]
  exact (norm_add_le _ _).trans (by linarith [hT.2 n A, hU.2 n A])

lemma completelyBounded_sum {I : Type*} [Fintype I]
    (T : I → M →L[ℂ] M) (C : I → ℝ) (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    CompletelyBoundedEstimate (∑ i, T i) (∑ i, C i) := by
  classical
  refine ⟨Finset.sum_nonneg (fun i _ => (hT i).1), fun n A => ?_⟩
  have he : A.map (∑ i, T i : M →L[ℂ] M) = ∑ i, A.map (T i) := by
    ext j k
    simp only [CStarMatrix.map_apply, sum_apply, cstar_finite_sum_apply]
  rw [he]
  exact (norm_sum_le _ _).trans (by
    simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun i _ => (hT i).2 n A))

def leftSandwichMap (a b : M) (T : M →L[ℂ] M) : M →L[ℂ] M :=
  (ContinuousLinearMap.mul ℂ M a).comp (T.comp (ContinuousLinearMap.mul ℂ M b))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma leftSandwichMap_apply (a b : M) (T : M →L[ℂ] M) (x : M) :
    leftSandwichMap a b T x = a * T (b * x) := rfl

omit [PartialOrder M] [StarOrderedRing M] in
lemma matrix_scalar_mul_apply {n : ℕ} (a : M) (A : CStarMatrix (Fin n) (Fin n) M)
    (i j : Fin n) : (matrixScalarHom n a * A) i j = a * A i j := by
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, ite_mul, zero_mul]
  simp

lemma completelyBounded_leftSandwich (a b : M) {T : M →L[ℂ] M} {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) :
    CompletelyBoundedEstimate (leftSandwichMap a b T) (‖a‖ * C * ‖b‖) := by
  refine ⟨mul_nonneg (mul_nonneg (norm_nonneg _) hT.1) (norm_nonneg _), fun n A => ?_⟩
  have he : A.map (leftSandwichMap a b T) =
      matrixScalarHom n a * ((matrixScalarHom n b * A).map T) := by
    ext i j
    simp only [CStarMatrix.map_apply, leftSandwichMap_apply, matrix_scalar_mul_apply]
  rw [he]
  have ha : ‖matrixScalarHom n a‖ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le _ _
  have hb : ‖matrixScalarHom n b‖ ≤ ‖b‖ := NonUnitalStarAlgHom.norm_apply_le _ _
  calc
    _ ≤ ‖matrixScalarHom n a‖ * ‖(matrixScalarHom n b * A).map T‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * (C * (‖b‖ * ‖A‖)) := by
      apply mul_le_mul ha _ (norm_nonneg _) (norm_nonneg _)
      exact (hT.2 n _).trans (mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))) hT.1)
    _ = _ := by ring

end BoundedHochschild.KadisonRingrose

end

end OAI
