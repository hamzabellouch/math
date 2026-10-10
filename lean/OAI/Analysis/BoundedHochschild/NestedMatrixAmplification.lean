import OAI.Analysis.BoundedHochschild.CompletelyBoundedRows

namespace OAI

/-! Nested finite matrix amplifications and their actual C*-norms. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

/-- Flattening two finite matrix indices is a star-algebra equivalence. -/
def nestedMatrixEquiv (n k : ℕ) :
    CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin k) (Fin k) M) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin n × Fin k) (Fin n × Fin k) M where
  toFun A i j := A i.1 j.1 i.2 j.2
  invFun A i j p q := A (i, p) (j, q)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl
  map_mul' A B := by
    ext i j
    change (∑ q : Fin n,
      (fun a b : Fin k => ∑ t : Fin k, A i.1 q a t * B q j.1 t b)) i.2 j.2 =
      ∑ q : Fin n × Fin k, A i.1 q.1 i.2 q.2 * B q.1 j.1 q.2 j.2
    simp only [Finset.sum_apply, Fintype.sum_prod_type]

variable [PartialOrder M] [StarOrderedRing M]

lemma nestedMatrix_norm (n k : ℕ)
    (A : CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin k) (Fin k) M)) :
    ‖nestedMatrixEquiv n k A‖ = ‖A‖ := StarAlgEquiv.norm_map (nestedMatrixEquiv n k) A

/-- Reindexing a finite square amplification preserves its norm. -/
lemma matrix_reindex_norm {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : CStarMatrix I I M) :
    ‖CStarMatrix.reindexₐ ℂ M e A‖ = ‖A‖ :=
  StarAlgEquiv.norm_map (CStarMatrix.reindexₐ ℂ M e) A

/-- The entrywise amplification of a bounded map is a bounded linear map
on each fixed finite matrix algebra. -/
def matrixAmplification (k : ℕ) (T : M →L[ℂ] M) :
    CStarMatrix (Fin k) (Fin k) M →L[ℂ] CStarMatrix (Fin k) (Fin k) M := by
  refine ⟨CStarMatrix.mapₗ T.toLinearMap, ?_⟩
  change Continuous (fun A : Fin k → Fin k → M => fun i j => T (A i j))
  exact continuous_pi fun i => continuous_pi fun j =>
    T.continuous.comp ((continuous_apply j).comp (continuous_apply i))

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma matrixAmplification_apply (k : ℕ) (T : M →L[ℂ] M)
    (A : CStarMatrix (Fin k) (Fin k) M) : matrixAmplification k T A = A.map T := rfl

lemma matrixAmplification_norm_le (k : ℕ) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : ‖matrixAmplification k T‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hT.1 (hT.2 k)

/-- A complete bound is unchanged by passing to any fixed finite
amplification. The proof flattens the two genuine matrix norms. -/
theorem matrixAmplification_completelyBounded (k : ℕ) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) :
    CompletelyBoundedEstimate (matrixAmplification k T) C := by
  refine ⟨hT.1, ?_⟩
  intro n A
  let e : Fin n × Fin k ≃ Fin (n * k) := finProdFinEquiv
  have heq :
      CStarMatrix.reindexₐ ℂ M e (nestedMatrixEquiv n k (A.map (matrixAmplification k T))) =
        (CStarMatrix.reindexₐ ℂ M e (nestedMatrixEquiv n k A)).map T := by
    ext i j
    rfl
  have hb := hT.2 (n * k) (CStarMatrix.reindexₐ ℂ M e (nestedMatrixEquiv n k A))
  rw [← heq, matrix_reindex_norm, nestedMatrix_norm,
    matrix_reindex_norm, nestedMatrix_norm] at hb
  exact hb

end BoundedHochschild.KadisonRingrose

end

end OAI
