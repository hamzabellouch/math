import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.CascadeBlockLaw
import OAI.Probability.SKBarriers.Hierarchy.RootCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootGradient_penalty_zero (m : Fin 0 → ℝ) (u : ℝ) {f : ParameterSpace 0 → ℝ}
    (hf : BoundedDerivs f) (x : ℝ) :
    rootGradient 0 (hierarchyPenalty 0 m u f) x=u*rootGradient 0 f x := by
  have hd := (hf.1.differentiable (by norm_num) x).hasFDerivAt.const_mul u
  change fderiv ℝ (fun z : ℝ => u*f z) x 1=u*fderiv ℝ f x 1
  rw [hd.fderiv]
  rfl

def rootResponse (n : ℕ) (m : Fin n → ℝ) (u : ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) : ℝ :=
  rootHessian n f z+u*(rootGradient n f z)^2-
    rootGradient n f z*rootGradient n (hierarchyPenalty n m u f) z

theorem gaussianAverage_rootResponse (n : ℕ) (m : Fin (n+1) → ℝ) (u : ℝ)
    {f : ParameterSpace (n+1) → ℝ} (hf : BoundedDerivs f) (z : ParameterSpace n) :
    gaussianAverage (m (Fin.last n)) f (rootResponse (n+1) m u f) z =
      rootResponse n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) f) z := by
  let q := m (Fin.last n)
  let G : ℝ → ℝ := fun y => rootGradient (n+1) f (z,y)
  let H : ℝ → ℝ := fun y => rootHessian (n+1) f (z,y)
  let μ := gaussianStepLaw q f z
  let P := rootGradient n (hierarchyPenalty n (fun i => m i.castSucc) q (gaussianStep q f)) z
  let := gaussianStepLaw_probability hf q z
  obtain ⟨hcG,B,_hB,hbG⟩ := prefixGradient_data hf (parameterAxis n)
  obtain ⟨hcH,C,_hC,hbH⟩ := prefixHessian_data hf (parameterAxis n) (parameterAxis n)
  have hmg : MemLp G 2 μ := MemLp.of_bound
    (hcG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable B
    (ae_of_all _ (fun y => hbG (z,y)))
  have iG : Integrable G μ := hmg.integrable one_le_two
  have iH : Integrable H μ := integrable_gaussianStep_of_bounded hf q z
    (hcH.comp (continuous_const.prodMk continuous_id)) (fun y => hbH (z,y))
  have he (y : ℝ) : rootResponse (n+1) m u f (z,y) = H y+q*(G y)^2-G y*P := by
    rw [rootResponse,rootGradient_penalty_succ n m u hf]
    change H y+u*(G y)^2-G y*((u-q)*G y+P)=_
    ring
  change (∫ y, rootResponse (n+1) m u f (z,y) ∂μ)=_
  simp_rw [he]
  have iHG : Integrable (fun y => H y+q*(G y)^2) μ := iH.add (hmg.integrable_sq.const_mul q)
  rw [integral_sub iHG (iG.mul_const P),
    integral_add iH (hmg.integrable_sq.const_mul q), integral_const_mul, integral_mul_const]
  have hG : rootGradient n (gaussianStep q f) z=∫ y, G y ∂μ :=
    fderiv_gaussianStep_apply hf q z (parameterAxis n)
  have hH : rootHessian n (gaussianStep q f) z=
      (∫ y, H y ∂μ)+q*((∫ y, G y*G y ∂μ)-(∫ y, G y ∂μ)*(∫ y, G y ∂μ)) :=
    fderiv_fderiv_gaussianStep_apply hf q z (parameterAxis n) (parameterAxis n)
  change _=rootHessian n (gaussianStep q f) z+q*(rootGradient n (gaussianStep q f) z)^2-
    rootGradient n (gaussianStep q f) z*P
  rw [hH,hG]
  simp only [pow_two]
  ring

theorem hierarchyPressure_rootHessian (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    rootHessian 0 (hierarchyPressure n m f) x=
      hierarchyAverage n m f (rootResponse n m u f) x := by
  induction n generalizing u with
  | zero =>
    change rootHessian 0 f x=rootResponse 0 m u f x
    rw [rootResponse,rootGradient_penalty_zero m u hf]
    ring
  | succ n ih =>
    change rootHessian 0 (hierarchyPressure n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)) x=
      hierarchyAverage n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
        (gaussianAverage (m (Fin.last n)) f (rootResponse (n+1) m u f)) x
    have he : gaussianAverage (m (Fin.last n)) f (rootResponse (n+1) m u f)=
        rootResponse n (fun i => m i.castSucc) (m (Fin.last n)) (gaussianStep (m (Fin.last n)) f) :=
      funext (gaussianAverage_rootResponse n m u hf)
    rw [he]
    exact ih (fun i => m i.castSucc) _ (hf.gaussianStep _)

end SK.Analytic

end
end

end OAI
