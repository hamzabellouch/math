import OAI.Analysis.PureInfiniteness.NonunitalFiniteCompression
import OAI.Analysis.PureInfiniteness.SpectralCopies

namespace OAI

/-! Off-diagonal estimates for the different copies of a spectral compressor. -/

noncomputable section

namespace WeakPureInfiniteness

variable {D J : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Fintype J]

lemma cross_column_norm_le (G K : CStarMatrix J (Fin 1) D)
    (hG : ‖G‖ ≤ 1) (hK : ‖K‖ ≤ 1) (X : CStarMatrix J J D) :
    ‖G.conjTranspose * X * K‖ ≤ ‖X‖ := by
  calc
    _ ≤ (‖G.conjTranspose‖ * ‖X‖) * ‖K‖ :=
      (rectangular_norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (rectangular_norm_mul_le _ _) (norm_nonneg _))
    _ = (‖G‖ * ‖X‖) * ‖K‖ := by rw [rectangular_norm_conjTranspose]
    _ ≤ (1 * ‖X‖) * 1 := by gcongr
    _ = _ := by ring

lemma norm_cross_compression_error (H : CStarMatrix (Fin 1) J D)
    (G K : CStarMatrix J (Fin 1) D) (hH : ‖H‖ ≤ 1) (hG : ‖G‖ ≤ 1) (hK : ‖K‖ ≤ 1)
    (X : CStarMatrix (Fin 1) (Fin 1) D) (S : CStarMatrix J J D) :
    ‖(H * G).conjTranspose * X * (H * K) - G.conjTranspose * (H.conjTranspose * H * S) * K‖ ≤
      ‖X * H - H * S‖ := by
  have he : (H * G).conjTranspose * X * (H * K) -
      G.conjTranspose * (H.conjTranspose * H * S) * K =
      G.conjTranspose * (H.conjTranspose * (X * H - H * S)) * K := by
    simp only [rectangular_conjTranspose_mul, rectangular_mul_sub,
      rectangular_sub_mul, rectangular_mul_assoc]
  rw [he]
  calc
    _ ≤ ‖H.conjTranspose * (X * H - H * S)‖ := cross_column_norm_le G K hG hK _
    _ ≤ ‖H.conjTranspose‖ * ‖X * H - H * S‖ := rectangular_norm_mul_le _ _
    _ ≤ 1 * ‖X * H - H * S‖ := by
      rw [rectangular_norm_conjTranspose]
      exact mul_le_mul_of_nonneg_right hH (norm_nonneg _)
    _ = _ := one_mul _

end WeakPureInfiniteness

end

end OAI
