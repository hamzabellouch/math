import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointDerivative
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraOneParameter
import Mathlib.Algebra.Lie.OfAssociative

namespace OAI

/-! # The adjoint exponential without a faithful representation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The intrinsic bracket, viewed as a continuous operator on the model space. -/
def groupAdjointOperator (v : GroupLieAlgebra (𝓘(ℝ, E)) G) : E →L[ℝ] E :=
  let d : E →ₗ[ℝ] E := LieModule.toEnd ℝ
    (GroupLieAlgebra (𝓘(ℝ, E)) G) (GroupLieAlgebra (𝓘(ℝ, E)) G) v
  d.toContinuousLinearMap

@[simp] theorem groupAdjointOperator_apply (v w : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    groupAdjointOperator (E := E) v w = ⁅v, w⁆ := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem adjointLinearMap_one :
    adjointLinearMap (E := E) (1 : G) = 1 :=
  (conjugationDifferentialHom (E := E)).map_one

omit [FiniteDimensional ℝ E] in
theorem adjointLinearMap_mul (a b : G) :
    adjointLinearMap (E := E) (a * b) = adjointLinearMap (E := E) a * adjointLinearMap b :=
  (conjugationDifferentialHom (E := E)).map_mul a b

theorem adjointLinearMap_exponential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (t : ℝ) :
    adjointLinearMap (E := E) (Exp (t • v)) =
      NormedSpace.exp (t • groupAdjointOperator (E := E) v) := by
  let C : ℝ → E →L[ℝ] E := fun s => adjointLinearMap (E := E) (Exp (s • v))
  have hC : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E →L[ℝ] E)) ∞ C :=
    contMDiff_conjugationDifferentialHom.comp (hExp.contMDiff_curve v)
  have hd : HasDerivAt C (deriv C 0) 0 := (hC.contDiff.differentiable (by simp) 0).hasDerivAt
  have he : deriv C 0 = groupAdjointOperator (E := E) v := by
    ext w
    have hp := hd.clm_apply (hasDerivAt_const (0 : ℝ) w)
    have hbr := hasDerivAt_adjoint_exponential_zero (E := E) hExp v w
    have hu := hp.unique hbr
    rw [map_zero, add_zero] at hu
    exact hu.trans (groupAdjointOperator_apply v w).symm
  rw [he] at hd
  have hzero : C 0 = 1 := by
    change adjointLinearMap (E := E) (Exp (0 • v)) = 1
    rw [zero_smul, hExp.map_zero, adjointLinearMap_one]
  have hadd (s u : ℝ) : C (s + u) = C s * C u := by
    change adjointLinearMap (E := E) (Exp ((s + u) • v)) = _
    rw [hExp.map_add_smul, adjointLinearMap_mul]
  exact oneParameter_eq_exp hzero hadd hd t

end PolycyclicRecognition

end

end OAI
