import OAI.Geometry.EinsteinFour.MatrixSlotCompression
import OAI.Geometry.EinsteinFour.RicciGradient

namespace OAI

/-! Pair the raw Ricci-commuted gradient with the varying matrix-slot
operator. The final square is the energy of the orthogonal compression. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

theorem matrixSlotOperator_compression_pairing (S : Shape) (v : ℝ)
    (p k l : Vec) (W : Tensor) (hw : W.traceFree) (hbw : W.bianchi) :
    inner ℝ (matrixSlotOperator (Matrix.diagonal (fun s => v * S.s s))
      (tensorGradientVector (parameters S p k l))) (tensorGradientVector W) =
        inner ℝ (tensorGradientVector (curvatureAction S v p k l))
          (tensorGradientVector W) := by
  rw [matrixSlotOperator_tensor S v _ (parameters_traceFree S p k l),
    inner_tensorGradientVector, inner_tensorGradientVector,
    curvatureAction_compression S v p k l W hw hbw]

/-- The matrix-slot pairing uses the uncompressed differential equation;
the coefficient `20` and compressed squared norm are consequences. -/
theorem matrixSlotOperator_ricci_pairing (S : Shape) (v : ℝ)
    (p k l : Vec) (L : Tensor) (hLz : L.traceFree) (hLb : L.bianchi)
    (hL : L.matrix = ricciGradient (fun s => v * S.s s) (parameters S p k l)) :
    inner ℝ (matrixSlotOperator (Matrix.diagonal (fun s => v * S.s s))
      (tensorGradientVector (parameters S p k l))) (tensorGradientVector L) =
        13 * (6 * curvatureBilinear S v (parameters S p k l) (parameters S p k l)) -
          20 * (curvatureAction S v p k l).squaredNorm := by
  have hC := ricciGradient_compressed_pairing S v p k l
    (curvatureAction S v p k l) (parameters_traceFree S _ _ _)
      (parameters_bianchi S _ _ _)
  rw [← hL, rawPairing_sub_left, rawPairing_smul_left,
    rawPairing_smul_left] at hC
  have hnorm : rawPairing (curvatureAction S v p k l).matrix
      (curvatureAction S v p k l).matrix = (curvatureAction S v p k l).squaredNorm := by
    rw [← inner_rawGradientVector]
    rw [real_inner_self_eq_norm_sq]
    exact tensorGradientVector_norm_sq _
  have hZ : rawPairing (parameters S p k l).matrix
      (curvatureAction S v p k l).matrix =
        6 * curvatureBilinear S v (parameters S p k l) (parameters S p k l) := by
    rw [rawPairing_comm, tensor_pairing_eq_raw,
      curvatureAction_compression S v p k l _ (parameters_traceFree S p k l)
        (parameters_bianchi S p k l),
      matrixCurvatureTensor_pairing S v _ _ (parameters_traceFree S p k l)]
  rw [matrixSlotOperator_compression_pairing S v p k l L hLz hLb,
    inner_tensorGradientVector, ← tensor_pairing_eq_raw,
    rawPairing_comm, hC, hnorm, hZ]

end
end PositiveEinsteinFour.Geometry

end OAI
