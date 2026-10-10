import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
import OAI.Probability.SKBarriers.Scalar.ScalarSplit

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarStepAverage_add_const (m v c : ℝ) (f g : ℝ → ℝ) :
    scalarStepAverage m v (fun z => f z+c) g=scalarStepAverage m v f g := by
  funext x
  simp only [scalarStepAverage,gaussianAverage,gaussianStepLaw]
  have he : (fun y => m*(f (x+v*y)+c))=fun y => m*f (x+v*y)+m*c := by
    funext y
    ring
  rw [he,tilted_add_constant]

theorem scalarHierarchyAverage_add_const (n : ℕ) (m v : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) (c : ℝ) :
    scalarHierarchyAverage n m v (fun z => f z+c) g=scalarHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [scalarHierarchyAverage,scalarStep_add_const hf,scalarStepAverage_add_const]
    exact ih _ _ (scalarStep_regular hf _ _) _

theorem scalarMomentSquare_add_const (n : ℕ) (m v : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) (c : ℝ) (j : Fin (n+1)) :
    scalarMomentSquare n m v (fun z => f z+c) g j=scalarMomentSquare n m v f g j := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last]
      exact scalarHierarchyAverage_add_const _ _ _ hf _ c
    · simp only [scalarMomentSquare,Fin.lastCases_castSucc,scalarStep_add_const hf,
        scalarStepAverage_add_const]
      exact ih _ _ (scalarStep_regular hf _ _) _ j

theorem scalarStepAverage_one_spin (v : ℝ) :
    scalarStepAverage 1 v scalarSpinTerminal scalarMagnetization=scalarMagnetization := by
  funext x
  have H := scalarHierarchy_gradient_average 1 (fun _ => (1:ℝ)) (fun _ => v)
    scalarSpinTerminal_regular scalarSpinTerminal_hasDerivAt x
  change deriv (scalarStep 1 v scalarSpinTerminal) x=scalarStepAverage 1 v scalarSpinTerminal scalarMagnetization x at H
  rw [scalarStep_one_spin] at H
  rw [((scalarSpinTerminal_hasDerivAt x).add_const (v^2/2)).deriv] at H
  exact H.symm

end SK.Analytic

end
end

end OAI
