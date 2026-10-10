import OAI.Analysis.BoundedHochschild.MatrixScalarColumns

namespace OAI

/-! Complete boundedness is preserved by finite normalized right averaging. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma finiteRowEstimate_of_columns {n : ℕ} [NeZero n]
    (c : Fin n → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (hs : ∑ i, (c i).final = 1) (T : M →L[ℂ] M) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) (x : Fin n → M) :
    ‖∑ i, T (x i) * star (T (x i))‖ ≤ C ^ 2 * ‖∑ i, x i * star (x i)‖ := by
  let k : Fin n := ⟨0, NeZero.pos n⟩
  have hmap : (columnCompression c ((c k : M) * columnRow c x)).map T =
      columnCompression c ((c k : M) * columnRow c (fun i => T (x i))) := by
    ext i j
    rw [CStarMatrix.map_apply, columnCompression_row c hi ho, columnCompression_row c hi ho]
    split_ifs <;> simp
  have hb := hT.2 n (columnCompression c ((c k : M) * columnRow c x))
  rw [hmap, columnCompression_norm c hi ho hs, columnCompression_norm c hi ho hs,
    left_isometry_norm (hi k), left_isometry_norm (hi k)] at hb
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, columnRow_norm_sq c hi ho, columnRow_norm_sq c hi ho] at hb2
  exact hb2

universe u
variable {N X : Type u} [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma matrixAmplification_rowBound (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N)
    (hno : NoFiniteCentralSummand N) (k : ℕ) (T : N →L[ℂ] N) {C : ℝ}
    (hT : CompletelyBoundedEstimate T C) : HasFiniteRowBound (matrixAmplification k T) C := by
  refine ⟨hT.1, ?_⟩
  intro n x
  cases n with
  | zero => simp
  | succ n =>
      obtain ⟨c, hi, ho, hs⟩ := exists_properlyInfinite_matrix_columns e hno (n + 1)
      obtain ⟨hdi, hdo, hds⟩ := matrixScalar_columns k c hi ho hs
      exact finiteRowEstimate_of_columns _ hdi hdo hds _
        (matrixAmplification_completelyBounded k T hT) x

omit [PartialOrder N] [StarOrderedRing N] in
lemma cstar_finite_sum_apply {I : Type*} [Fintype I] {n : ℕ}
    (f : I → CStarMatrix (Fin n) (Fin n) N) (i j : Fin n) :
    (∑ t, f t) i j = ∑ t, f t i j := by
  classical
  exact Matrix.sum_apply i j Finset.univ (fun t => CStarMatrix.ofMatrix.symm (f t))

omit [PartialOrder N] [StarOrderedRing N] in
lemma matrix_mul_scalar_apply {k : ℕ} (A : CStarMatrix (Fin k) (Fin k) N)
    (b : N) (i j : Fin k) : (A * matrixScalarHom k b) i j = A i j * b := by
  simp only [CStarMatrix.mul_apply, matrixScalarHom_apply, mul_ite, mul_zero]
  simp

lemma matrixAmplification_rightAverage {I : Type*} [Fintype I]
    (k : ℕ) (m : I → N) (T : N →L[ℂ] N) :
    matrixAmplification k (finiteRightAverage m T) =
      finiteRightAverage (fun i => matrixScalarHom k (m i)) (matrixAmplification k T) := by
  ext A i j
  simp only [matrixAmplification_apply, CStarMatrix.map_apply, finiteRightAverage_apply,
    cstar_finite_sum_apply, ← map_star, matrix_mul_scalar_apply]

omit [PartialOrder N] [StarOrderedRing N] in
lemma matrixScalar_normalized {I : Type*} [Fintype I] (k : ℕ) (m : I → N)
    (hm : ∑ i, m i * star (m i) = 1) :
    ∑ i, matrixScalarHom k (m i) * star (matrixScalarHom k (m i)) = 1 := by
  simpa only [map_sum, map_mul, map_star, map_one] using congrArg (matrixScalarHom k) hm

/-- Finite normalized right averages preserve the original complete bound,
not only its level-one operator norm consequence. -/
theorem finiteRightAverage_completelyBounded {n : ℕ}
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] N) (hno : NoFiniteCentralSummand N)
    (m : Fin (n + 1) → N) (hm : ∑ i, m i * star (m i) = 1)
    (T : N →L[ℂ] N) {C : ℝ} (hT : CompletelyBoundedEstimate T C) :
    CompletelyBoundedEstimate (finiteRightAverage m T) C := by
  refine ⟨hT.1, ?_⟩
  intro k A
  have hnorm : ‖matrixAmplification k (finiteRightAverage m T)‖ ≤ C := by
    rw [matrixAmplification_rightAverage]
    obtain ⟨c, hi, ho, hs⟩ := exists_properlyInfinite_matrix_columns e hno (n + 1)
    obtain ⟨hdi, hdo, _⟩ := matrixScalar_columns k c hi ho hs
    exact finiteRightAverage_norm_of_rowBound _ hdi hdo _ (matrixScalar_normalized k m hm)
      _ (matrixAmplification_rowBound e hno k T hT)
  exact ((matrixAmplification k (finiteRightAverage m T)).le_opNorm A).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg A))

end BoundedHochschild.KadisonRingrose

end

end OAI
