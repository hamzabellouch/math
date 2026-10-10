import OAI.Analysis.Pureness.Comparison.RootRankIdentification
import OAI.Analysis.Pureness.Stabilization.MatrixStageTrace

namespace OAI
noncomputable section
open scoped ComplexOrder ENNReal NNReal CStarAlgebra Topology
open Filter
namespace CuntzComparison
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def TracialState.extendedTrace (τ : TracialState A) : ExtendedTrace A where
  toFun a := ENNReal.ofReal (τ.toPositiveLinearMap a.1).re
  map_zero := by simp [Positive.zero]
  map_add a b := by
    change ENNReal.ofReal (τ.toPositiveLinearMap (a.1+b.1)).re = _
    rw [map_add, Complex.add_re, ENNReal.ofReal_add
      (Complex.nonneg_iff.mp (τ.toPositiveLinearMap.map_nonneg a.2)).1
      (Complex.nonneg_iff.mp (τ.toPositiveLinearMap.map_nonneg b.2)).1]
  map_smul r a := by
    change ENNReal.ofReal (τ.toPositiveLinearMap ((r : ℝ) • a.1)).re = _
    rw [← Complex.coe_smul, map_smul]
    simp only [smul_eq_mul, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      _ = ENNReal.ofReal (r : ℝ) * ENNReal.ofReal (τ.toPositiveLinearMap a.1).re := ENNReal.ofReal_mul r.2
      _ = _ := by rw [ENNReal.ofReal_coe_nnreal]
  tracial x := by
    change ENNReal.ofReal (τ.toPositiveLinearMap (star x*x)).re = _
    rw [τ.tracial]
    rfl
  lowerSemicontinuous := by
    apply Continuous.lowerSemicontinuous
    exact ENNReal.continuous_ofReal.comp
      (Complex.continuous_re.comp ((map_continuous τ.toPositiveLinearMap).comp continuous_subtype_val))

@[simp] lemma TracialState.extendedTrace_apply (τ : TracialState A) (a : Positive A) :
    τ.extendedTrace a = ENNReal.ofReal (τ.toPositiveLinearMap a.1).re := rfl

theorem TracialState.extended_matrixTrace (τ : TracialState A) {n : ℕ} (a : Positive (FinMatrix A n)) :
    τ.extendedTrace.matrixTrace (Fin n) a = ENNReal.ofReal (τ.matrixTraceLinear a.1).re := by
  rw [ExtendedTrace.matrixTrace_apply]
  simp only [extendedTrace_apply, Positive.matrixDiagonal, matrixTraceLinear,
    LinearMap.coe_mk, AddHom.coe_mk, Complex.re_sum]
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro i _
  exact (Complex.nonneg_iff.mp (τ.toPositiveLinearMap.map_nonneg (Positive.matrix_diagonal_nonneg a i))).1
end CuntzComparison

end

end OAI
