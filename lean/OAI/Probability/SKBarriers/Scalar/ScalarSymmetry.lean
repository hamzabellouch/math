import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarSpinRecursion

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarStep_even {f : ℝ → ℝ} (hf : Function.Even f) (m v : ℝ) :
    Function.Even (scalarStep m v f) := by
  intro z
  have he (y : ℝ) : f (-z+v*y) = f (z+v*(-y)) := by
    rw [← hf (-z+v*y)]
    congr 1
    ring
  have hi (g : ℝ → ℝ) : (∫ y, g (-y) ∂gaussianReal 0 1) = ∫ y, g y ∂gaussianReal 0 1 := by
    simpa only [scalarSign_true] using
      (scalarSign_gaussian true).integral_comp (scalarSignEquiv true).measurableEmbedding g
  simp only [scalarStep,gaussianStep,positiveGaussianLogStep,he]
  rw [hi (fun y => f (z+v*y)),hi (fun y => Real.exp (m*f (z+v*y)))]

theorem scalarHierarchy_even (n : ℕ) (m v : Fin n → ℝ) {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih => exact ih _ _ (scalarStep_even hf _ _)

theorem scalarHierarchy_spin_even (n : ℕ) (m v : Fin n → ℝ) :
    Function.Even (scalarHierarchy n m v scalarSpinTerminal) :=
  scalarHierarchy_even n m v (fun z => by simp only [scalarSpinTerminal,Real.cosh_neg])

theorem scalarHierarchy_spin_gradient_zero (n : ℕ) (m v : Fin n → ℝ) :
    fderiv ℝ (scalarHierarchy n m v scalarSpinTerminal) 0 1 = 0 := by
  let f := scalarHierarchy n m v scalarSpinTerminal
  have hf : BoundedDerivs f := scalarHierarchy_spin_regular n m v
  have hD := ((hf.1.differentiable (by norm_num)) 0).hasDerivAt
  have hD' : HasDerivAt f (deriv f 0) (-(0:ℝ)) := by simpa only [neg_zero] using hD
  have H := hD'.comp (0:ℝ) (hasDerivAt_neg (0:ℝ))
  have he : (fun x => f (-x)) = f := funext (scalarHierarchy_spin_even n m v)
  change HasDerivAt (fun x => f (-x)) (deriv f 0 * (-1)) 0 at H
  rw [he] at H
  have hh := H.unique hD
  change deriv f 0 = 0
  linarith
end SK.Analytic

end
end

end

end OAI
