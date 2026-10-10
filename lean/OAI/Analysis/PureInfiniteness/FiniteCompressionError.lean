import OAI.Analysis.PureInfiniteness.ColumnReturnEstimates

namespace OAI

/-! The finite compression estimate in the joint spectral argument. The row
error controls preservation by the resulting contractive compression. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype J]

lemma norm_row_column_le_one (H : CStarMatrix (Fin 1) J A)
    (G : CStarMatrix J (Fin 1) A) (hH : ‖H‖ ≤ 1) (hG : ‖G‖ ≤ 1) :
    ‖H * G‖ ≤ 1 := by
  exact (rectangular_norm_mul_le H G).trans
    ((mul_le_mul hH hG (norm_nonneg G) zero_le_one).trans_eq (one_mul 1))

lemma norm_finite_compression_error (H : CStarMatrix (Fin 1) J A)
    (G : CStarMatrix J (Fin 1) A) (hH : ‖H‖ ≤ 1) (hG : ‖G‖ ≤ 1)
    (X : CStarMatrix (Fin 1) (Fin 1) A) (S : CStarMatrix J J A) :
    ‖(H * G).conjTranspose * X * (H * G) -
        columnReturn G (H.conjTranspose * H * S)‖ ≤ ‖X * H - H * S‖ := by
  have he : (H * G).conjTranspose * X * (H * G) -
      columnReturn G (H.conjTranspose * H * S) =
      columnReturn G (H.conjTranspose * (X * H - H * S)) := by
    simp only [columnReturn, rectangular_conjTranspose_mul, rectangular_mul_sub,
      rectangular_sub_mul, rectangular_mul_assoc]
  rw [he]
  calc
    _ ≤ ‖H.conjTranspose * (X * H - H * S)‖ := columnReturn_norm_le G hG _
    _ ≤ ‖H.conjTranspose‖ * ‖X * H - H * S‖ := rectangular_norm_mul_le _ _
    _ ≤ 1 * ‖X * H - H * S‖ := by
      rw [rectangular_norm_conjTranspose]
      exact mul_le_mul_of_nonneg_right hH (norm_nonneg _)
    _ = _ := one_mul _

lemma norm_finite_compression_preservation (H : CStarMatrix (Fin 1) J A)
    (G : CStarMatrix J (Fin 1) A) (hH : ‖H‖ ≤ 1) (hG : ‖G‖ ≤ 1)
    (X : CStarMatrix (Fin 1) (Fin 1) A) (S : CStarMatrix J J A)
    (ε η : ℝ) (hrow : ‖X * H - H * S‖ ≤ ε)
    (hreturn : ‖columnReturn G (H.conjTranspose * H * S) - X‖ ≤ η) :
    ‖(H * G).conjTranspose * X * (H * G) - X‖ ≤ ε + η := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add ((norm_finite_compression_error H G hH hG X S).trans hrow) hreturn)

end WeakPureInfiniteness

end

end OAI
