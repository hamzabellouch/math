import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.PrincipalTransport

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Set LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] in
lemma linearSchwartz_inverse_comp (A : E ≃L[ℝ] E) (ψ : 𝓢(E,ℂ)) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A ψ) = ψ := by
  ext x
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply]

omit [CompleteSpace F] in

lemma linear_local_schwartz_system (A : E ≃L[ℝ] E)
    {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (d : ι → E) (g : ι → ι → 𝓢(E,ℂ))
    (b : κ → 𝓢(E,ℂ)) (L : κ → F →L[ℂ] F) (v : κ → E)
    (c : τ → 𝓢(E,ℂ)) (K : τ → F →L[ℂ] F) (u f : 𝓢(E,F)) (ψ : 𝓢(E,ℂ))
    (heq : smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A ψ)
      (-directionalPrincipal d g (u : 𝓢'(E,F)) + matrixLowerOrder b L v c K (u : 𝓢'(E,F))) =
      smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A ψ) (f : 𝓢'(E,F))) :
    smulLeftCLM F ψ
      (-directionalPrincipal (fun i => A (d i))
          (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (g i j))
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u : 𝓢'(E,F)) +
        matrixLowerOrder (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i))
          L (fun i => A (v i))
          (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)) K
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u : 𝓢'(E,F))) =
      smulLeftCLM F ψ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm f : 𝓢'(E,F)) := by
  have hs := congrArg (linearDistribution A) heq
  rw [linearDistribution_product,linearDistribution_product,
    linearSchwartz_inverse_comp,map_add,map_neg,directionalPrincipal_linear,matrixLowerOrder_linear,
    linearDistribution_schwartz,linearDistribution_schwartz] at hs
  have hh : |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| ≠ 0 :=
    abs_ne_zero.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)
  apply (smul_right_injective (M := 𝓢'(E,F)) hh)
  dsimp only [directionalPrincipal,matrixLowerOrder] at hs ⊢
  simp only [lineDerivOp_smul,ContinuousLinearMap.map_smul_of_tower,
    ← Finset.smul_sum,← smul_neg,← smul_add] at hs
  simpa only [ContinuousLinearMap.map_smul_of_tower] using hs
end TamingCompatibility.HilbertSobolev

end

end OAI
