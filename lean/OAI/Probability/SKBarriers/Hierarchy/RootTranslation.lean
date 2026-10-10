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

def rootTranslate (n : ℕ) (t : ℝ) (f : ParameterSpace n → ℝ) : ParameterSpace n → ℝ :=
  fun z => f (t • parameterAxis n+z)

theorem rootTranslate_regular (n : ℕ) (t : ℝ) {f : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) : BoundedDerivs (rootTranslate n t f) := hf.translate _

theorem rootGradient_translate (n : ℕ) (t : ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) :
    rootGradient n (rootTranslate n t f) z=rootGradient n f (t • parameterAxis n+z) := by
  exact congrArg (fun L : ParameterSpace n →L[ℝ] ℝ => L (parameterAxis n))
    (fderiv_comp_add_left (t • parameterAxis n))

theorem rootHessian_translate (n : ℕ) (t : ℝ) (f : ParameterSpace n → ℝ)
    (z : ParameterSpace n) :
    rootHessian n (rootTranslate n t f) z=rootHessian n f (t • parameterAxis n+z) := by
  have he : fderiv ℝ (rootTranslate n t f)=fun z => fderiv ℝ f (t • parameterAxis n+z) := by
    funext z
    exact fderiv_comp_add_left _
  unfold rootHessian
  rw [he,fderiv_comp_add_left]

theorem RootSpinCurvature.translate {n : ℕ} {f : ParameterSpace n → ℝ}
    (h : RootSpinCurvature n f) (t : ℝ) : RootSpinCurvature n (rootTranslate n t f) := by
  intro z
  rw [rootHessian_translate,rootGradient_translate]
  exact h _

theorem gaussianStep_rootTranslate (n : ℕ) (m t : ℝ) (f : ParameterSpace (n+1) → ℝ) :
    gaussianStep m (rootTranslate (n+1) t f)=rootTranslate n t (gaussianStep m f) := by
  funext z
  have he (y : ℝ) : rootTranslate (n+1) t f (z,y)=f (t • parameterAxis n+z,y) := by
    simp only [rootTranslate,parameterAxis,Prod.smul_mk,smul_zero,Prod.mk_add_mk,zero_add]
  simp only [gaussianStep,positiveGaussianLogStep,rootTranslate,parameterAxis,
    Prod.smul_mk,smul_zero,Prod.mk_add_mk,zero_add]

theorem hierarchyPressure_rootTranslate (n : ℕ) (m : Fin n → ℝ) (t : ℝ)
    (f : ParameterSpace n → ℝ) :
    hierarchyPressure n m (rootTranslate n t f)=rootTranslate 0 t (hierarchyPressure n m f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change hierarchyPressure n (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (rootTranslate (n+1) t f))=_
    rw [gaussianStep_rootTranslate,ih]
    rfl

theorem hierarchyPenalty_rootTranslate (n : ℕ) (m : Fin n → ℝ) (u t : ℝ)
    (f : ParameterSpace n → ℝ) :
    hierarchyPenalty n m u (rootTranslate n t f)=rootTranslate n t (hierarchyPenalty n m u f) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    funext z
    change (u-m (Fin.last n))*rootTranslate (n+1) t f z+
      hierarchyPenalty n (fun i => m i.castSucc) (m (Fin.last n))
        (gaussianStep (m (Fin.last n)) (rootTranslate (n+1) t f)) z.1=_
    rw [gaussianStep_rootTranslate,ih]
    rfl

end SK.Analytic

end
end

end OAI
