import OAI.Analysis.Laughlin.FiniteFlux.Error08
import OAI.Analysis.Laughlin.FiniteFlux.Gram08
import OAI.Analysis.Laughlin.FiniteFlux.LDLData08
import OAI.Analysis.Laughlin.FourBody.NumericBridge

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem ldl_8_0_0 : compressedRational 8 0 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 0 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_1 : compressedRational 8 0 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 1 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_2 : compressedRational 8 0 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 2 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_0_3 : compressedRational 8 0 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 0 3 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_0 : compressedRational 8 1 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 0 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_1 : compressedRational 8 1 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 1 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_2 : compressedRational 8 1 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 2 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_1_3 : compressedRational 8 1 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 1 3 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_0 : compressedRational 8 2 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 0 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_1 : compressedRational 8 2 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 1 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_2 : compressedRational 8 2 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 2 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_2_3 : compressedRational 8 2 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 2 3 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_0 : compressedRational 8 3 0 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 0 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_1 : compressedRational 8 3 1 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 1 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_2 : compressedRational 8 3 2 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 2 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem ldl_8_3_3 : compressedRational 8 3 3 =
    (lower_8 * Matrix.diagonal pivots_8 * lower_8.transpose) 3 3 := by
  rw [compressedRational_eq_compute, error_8, gram_8]
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
