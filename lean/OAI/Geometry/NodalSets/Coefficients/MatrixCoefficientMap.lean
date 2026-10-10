import OAI.Geometry.NodalSets.Charts.SphereChartVolume
import OAI.Geometry.NodalSets.Elliptic.PositiveContravariant

namespace OAI

namespace Yau.Target
open Matrix Yau.Geometry
open scoped RealInnerProductSpace ContDiff
noncomputable section

def baseCovectorCoordinates (α : BaseModel →L[ℝ] ℝ) : Fin 4 → ℝ :=
  fun i ↦ α (EuclideanSpace.basisFun (Fin 4) ℝ i)

lemma baseCovectorCoordinates_apply (α : BaseModel →L[ℝ] ℝ) (v : BaseModel) :
    α v = baseCovectorCoordinates α ⬝ᵥ WithLp.ofLp v := by
  have hv := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v
  conv_lhs => rw [← hv]
  simp [baseCovectorCoordinates,map_sum,map_smul,dotProduct,mul_comm]

lemma baseCovectorCoordinates_injective : Function.Injective baseCovectorCoordinates := by
  intro α β h
  ext v
  rw [baseCovectorCoordinates_apply,baseCovectorCoordinates_apply,h]

lemma baseCovectorCoordinates_ne_zero {α : BaseModel →L[ℝ] ℝ} (hα : α ≠ 0) :
    baseCovectorCoordinates α ≠ 0 := by
  intro h
  exact hα (baseCovectorCoordinates_injective (h.trans (by ext i; rfl)))

def matrixContravariant (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel :=
  ∑ i, ∑ j, A i j • (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.basisFun (Fin 4) ℝ j)).smulRight (EuclideanSpace.basisFun (Fin 4) ℝ i)

lemma matrixContravariant_coordinates (A : Matrix (Fin 4) (Fin 4) ℝ)
    (α : BaseModel →L[ℝ] ℝ) :
    WithLp.ofLp (matrixContravariant A α) = A *ᵥ baseCovectorCoordinates α := by
  ext k
  simp [matrixContravariant,baseCovectorCoordinates,mulVec,dotProduct,
    EuclideanSpace.basisFun_apply,Pi.single_apply,ite_mul,mul_ite,mul_comm]

lemma matrixContravariant_pair (A : Matrix (Fin 4) (Fin 4) ℝ) (α β : BaseModel →L[ℝ] ℝ) :
    α (matrixContravariant A β) = baseCovectorCoordinates α ⬝ᵥ (A *ᵥ baseCovectorCoordinates β) := by
  rw [baseCovectorCoordinates_apply,matrixContravariant_coordinates]

lemma matrixContravariant_positive (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosDef)
    (α : BaseModel →L[ℝ] ℝ) (hα : α ≠ 0) : 0 < α (matrixContravariant A α) := by
  rw [matrixContravariant_pair]
  simpa only [star_trivial] using hA.dotProduct_mulVec_pos (baseCovectorCoordinates_ne_zero hα)

def matrixCovariant (B : Matrix (Fin 4) (Fin 4) ℝ) :
    BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ :=
  ∑ i, ∑ j, B i j • (innerSL ℝ (EuclideanSpace.basisFun (Fin 4) ℝ j)).smulRight
    (innerSL ℝ (EuclideanSpace.basisFun (Fin 4) ℝ i))

lemma matrixCovariant_coordinates (B : Matrix (Fin 4) (Fin 4) ℝ) (v : BaseModel) :
    baseCovectorCoordinates (matrixCovariant B v) = B *ᵥ WithLp.ofLp v := by
  ext k
  simp [baseCovectorCoordinates,matrixCovariant,
    EuclideanSpace.inner_single_left,mulVec,dotProduct,mul_comm]

lemma matrixCovariant_apply (B : Matrix (Fin 4) (Fin 4) ℝ) (v w : BaseModel) :
    matrixCovariant B v w = (B *ᵥ WithLp.ofLp v) ⬝ᵥ WithLp.ofLp w := by
  rw [baseCovectorCoordinates_apply,matrixCovariant_coordinates]

lemma matrixContravariant_inverse (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : IsUnit A.det) :
    ContinuousLinearMap.inverse (matrixContravariant A) = matrixCovariant A⁻¹ := by
  apply ContinuousLinearMap.inverse_eq
  · ext v i
    change (matrixContravariant A (matrixCovariant A⁻¹ v)) i = v i
    have h := matrixContravariant_coordinates A (matrixCovariant A⁻¹ v)
    rw [matrixCovariant_coordinates,mulVec_mulVec,mul_nonsing_inv A hA,one_mulVec] at h
    exact congrFun h i
  · ext α v
    have h : baseCovectorCoordinates (matrixCovariant A⁻¹ (matrixContravariant A α)) =
        baseCovectorCoordinates α := by
      rw [matrixCovariant_coordinates,matrixContravariant_coordinates,mulVec_mulVec,
        nonsing_inv_mul A hA,one_mulVec]
    exact congrArg (fun β : BaseModel →L[ℝ] ℝ ↦ β v) (baseCovectorCoordinates_injective h)

lemma matrixCovariant_smul (r : ℝ) (B : Matrix (Fin 4) (Fin 4) ℝ) :
    matrixCovariant (r • B) = r • matrixCovariant B := by
  ext v w
  simp [matrixCovariant_apply,smul_mulVec,smul_dotProduct]

lemma coefficientMetric_matrix (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.PosDef) (ρ : ℝ) :
    coefficientMetricValue (matrixContravariant A,ρ) = matrixCovariant (ρ • A⁻¹) := by
  rw [coefficientMetricValue,matrixContravariant_inverse A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    matrixCovariant_smul]

end
end Yau.Target

end OAI
