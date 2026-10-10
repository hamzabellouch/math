import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.CascadeBlockLaw
import OAI.Probability.SKBarriers.Calculus.ParameterRecursion
import OAI.Probability.SKBarriers.Calculus.ParameterStepDerivative

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyParameterDerivative
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hierarchyPressure_parameterDerivative (n : ℕ) (m : Fin n → ℝ)
    (f : P × ParameterSpace n → ℝ) (hf : ParamRegular f) (z : P × ℝ) (v : P) :
    fderiv ℝ (fun z : P × ℝ => hierarchyPressure n m (fun w => f (z.1,w)) z.2) z (v,0) =
      hierarchyAverage n m (fun w => f (z.1,w))
        (fun w => fderiv ℝ f (z.1,w) (v,0)) z.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let g := gaussianStep (m (Fin.last n))
      (fun w : (P × ParameterSpace n) × ℝ => f (w.1.1,(w.1.2,w.2)))
    have hg : ParamRegular g := hf.gaussianStep _
    have hrec := ih (fun i => m i.castSucc) g hg
    change fderiv ℝ (fun z : P × ℝ => hierarchyPressure n (fun i => m i.castSucc)
      (fun w => g (z.1,w)) z.2) z (v,0) = _
    rw [hrec]
    have he : (fun w => fderiv ℝ g (z.1,w) (v,0)) = fun w : ParameterSpace n =>
        gaussianAverage (m (Fin.last n)) (fun w => f (z.1,w))
          (fun w => fderiv ℝ f (z.1,w) (v,0)) w := by
      funext w
      exact hf.parameterDerivative_gaussianStep _ (z.1,w) v
    rw [he]
    rfl

theorem parameterFDeriv_at_field {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : P × E → ℝ} (hf : Differentiable ℝ f) (p v : P) (y : E) :
    fderiv ℝ (fun p => f (p,y)) p v = fderiv ℝ f (p,y) (v,0) := by
  have hh : HasFDerivAt (fun a : P => (a,y)) (ContinuousLinearMap.inl ℝ P E) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const y p)
  have h := ((hf (p,y)).hasFDerivAt.comp p hh).fderiv
  change fderiv ℝ (fun p => f (p,y)) p = _ at h
  rw [h]
  rfl

end HierarchyParameterDerivative
end SK.Analytic

end
end

end

end OAI
