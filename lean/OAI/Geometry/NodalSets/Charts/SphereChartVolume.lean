import OAI.Geometry.NodalSets.Charts.RadialMetricIdentification
import OAI.Geometry.NodalSets.Charts.TangentGramDeterminant

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section
local instance : Fact (Module.finrank ℝ AmbientBase = 4+1) := ⟨by simp [AmbientBase]⟩
abbrev BaseModel := EuclideanSpace ℝ (Fin 4)

def sphereChartDerivative (p : Base) (y : BaseModel) : BaseModel →L[ℝ] AmbientBase :=
  (sphereAmbientDerivative ((extChartAt (𝓡 4) p).symm y)).comp
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm y)

def sphereChartFrame (p : Base) (y : BaseModel) : Matrix (Fin 5) (Fin 4) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis (sphereChartDerivative p y).toLinearMap

lemma sphereChartFrame_apply (p : Base) (y : BaseModel) (i : Fin 5) (j : Fin 4) :
    sphereChartFrame p y i j =
      sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ j) i := by
  simp [sphereChartFrame,LinearMap.toMatrix_apply]

lemma sphereChartFrame_mulVec (p : Base) (y : BaseModel) (v : Fin 4 → ℝ) :
    sphereChartFrame p y *ᵥ v =
      (fun i ↦ sphereChartDerivative p y (WithLp.toLp 2 v) i) := by
  exact LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis (sphereChartDerivative p y).toLinearMap
      (WithLp.toLp 2 v)

lemma sphereChartDerivative_injective (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    Function.Injective (sphereChartDerivative p y) := by
  apply (injective_mvfderiv_subtypeVal_sphere (n := 4) ((extChartAt (𝓡 4) p).symm y)).comp
  have h := (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 4) hy).injective
  rw [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
  convert! h using 1

lemma sphereChartFrame_injective (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    Function.Injective (sphereChartFrame p y).mulVec := by
  intro v w h
  rw [sphereChartFrame_mulVec,sphereChartFrame_mulVec] at h
  have he : sphereChartDerivative p y (WithLp.toLp 2 v) =
      sphereChartDerivative p y (WithLp.toLp 2 w) := by ext i; exact congrFun h i
  exact congrArg WithLp.ofLp (sphereChartDerivative_injective p hy he)

lemma sphereChartFrame_orthogonal (p : Base) (y : BaseModel) :
    (sphereChartFrame p y).transpose *ᵥ
      (fun i ↦ ((extChartAt (𝓡 4) p).symm y : AmbientBase) i) = 0 := by
  ext j
  have h := sphere_derivative_radial_orthogonal ((extChartAt (𝓡 4) p).symm y)
    (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p).symm y
      (EuclideanSpace.basisFun (Fin 4) ℝ j))
  simp only [mulVec,transpose_apply,sphereChartFrame_apply,sphereChartDerivative,
    Pi.zero_apply]
  rw [dotProduct_comm]
  convert! h using 1

lemma sphere_radial_dot (x : Base) :
    (fun i ↦ (x : AmbientBase) i) ⬝ᵥ (fun i ↦ (x : AmbientBase) i) = 1 := by
  have hn := mem_sphere_zero_iff_norm.mp x.property
  have h := real_inner_self_eq_norm_sq (x : AmbientBase)
  rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,hn,one_pow] at h
  exact h

def sphereRoundChartMatrix (p : Base) (y : BaseModel) : Matrix (Fin 4) (Fin 4) ℝ :=
  (sphereChartFrame p y).transpose * sphereChartFrame p y

def sphereWeightedChartMatrix (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (p : Base) (y : BaseModel) : Matrix (Fin 4) (Fin 4) ℝ :=
  (sphereChartFrame p y).transpose * weightedBaseMatrix A rho * sphereChartFrame p y

lemma sphereRoundChartMatrix_posDef (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) : (sphereRoundChartMatrix p y).PosDef := by
  simpa [sphereRoundChartMatrix,conjTranspose_eq_transpose_of_trivial] using
    (PosDef.one : (1 : Matrix (Fin 5) (Fin 5) ℝ).PosDef).conjTranspose_mul_mul_same
      (sphereChartFrame_injective p hy)

lemma sphereWeightedChartMatrix_posDef (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target) :
    (sphereWeightedChartMatrix A rho p y).PosDef := by
  simpa [sphereWeightedChartMatrix,conjTranspose_eq_transpose_of_trivial] using
    (weightedBaseMatrix_posDef hA hr).conjTranspose_mul_mul_same (sphereChartFrame_injective p hy)

lemma sphere_chart_determinant_ratio (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target)
    (hx : A *ᵥ (fun i ↦ ((extChartAt (𝓡 4) p).symm y : AmbientBase) i) =
      (fun i ↦ ((extChartAt (𝓡 4) p).symm y : AmbientBase) i)) :
    (sphereWeightedChartMatrix A rho p y).det / (sphereRoundChartMatrix p y).det =
      rho^4 / A.det := by
  have h := radial_tangent_gram_det A hA hr _ (sphereChartFrame p y) hx
    (sphere_radial_dot _) (sphereChartFrame_orthogonal p y)
  exact (div_eq_iff (sphereRoundChartMatrix_posDef p hy).det_pos.ne').mpr h

lemma sphere_chart_volume_ratio (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target)
    (hx : A *ᵥ (fun i ↦ ((extChartAt (𝓡 4) p).symm y : AmbientBase) i) =
      (fun i ↦ ((extChartAt (𝓡 4) p).symm y : AmbientBase) i)) :
    Real.sqrt (sphereWeightedChartMatrix A rho p y).det /
      Real.sqrt (sphereRoundChartMatrix p y).det = rho^2 / Real.sqrt A.det := by
  rw [← Real.sqrt_div (sphereWeightedChartMatrix_posDef A hA hr p hy).det_pos.le,
    sphere_chart_determinant_ratio A hA hr p hy hx,
    Real.sqrt_div (by positivity),show rho^4 = (rho^2)^2 by ring,Real.sqrt_sq (sq_nonneg rho)]

end
end Yau.Target

end OAI
