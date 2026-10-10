import OAI.Geometry.EinsteinFour.JacobiCurvatureCap
import OAI.Geometry.EinsteinFour.FlatDirichletNormalizer
import OAI.Geometry.EinsteinFour.DeterminantCompression

namespace OAI

/-! A fixed integrable bound for every positive normalized discrete determinant. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flat_kernel_det_mem_Ioc {N : ℕ} (t : ℝ) (R : Fin N → NormalMatrix)
    (hR : ∀ i, (R i).PosSemidef ∧ (R i).trace = 3)
    (hscalar : (1 - (3 : ℝ) • scaledFlatGreen t N).PosDef) :
    (1 - curvatureKernel (scaledFlatGreen t N) R).det ∈ Set.Ioc (0 : ℝ) 1 := by
  let H := symmetricCurvatureKernel (flatGreenRoot t N) R
  have hp : (1 - H).PosDef := symmetricCurvatureKernel_one_sub_posDef _ _
    (flatGreenRoot_square t N) (flatGreenRoot_transpose t N) hscalar R hR
  have hH : H.PosSemidef := symmetricCurvatureKernel_posSemidef _
    (flatGreenRoot_transpose t N) R (fun i => (hR i).1)
  have he : (1 - H).det = (1 - curvatureKernel (scaledFlatGreen t N) R).det :=
    symmetricCurvatureKernel_det _ _ (flatGreenRoot_square t N) R
  rw [← he]
  refine ⟨hp.det_pos, det_le_one_of_trace_le_card hp.posSemidef ?_⟩
  rw [Matrix.trace_sub, Matrix.trace_one]
  linarith [hH.trace_nonneg]

end
end PositiveEinsteinFour.Jacobi

end OAI
