import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem det_id_add_rankOne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (d : E) (L : E →L[ℝ] ℝ) :
    (ContinuousLinearMap.id ℝ E + L.smulRight d).det = 1 + L d := by
  let b := Module.finBasis ℝ E
  change LinearMap.det (LinearMap.id + L.toLinearMap.smulRight d) = _
  rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_smulRight, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  conv_rhs => rw [← b.sum_repr d, map_sum]
  simp only [dotProduct, Function.comp_apply, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  change L (b i) * (b.repr d) i = (b.repr d) i * L (b i)
  ring

end ScalarConductivity

end

end OAI
