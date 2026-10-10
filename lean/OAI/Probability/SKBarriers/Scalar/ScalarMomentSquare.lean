import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarTiltedExpectation

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarMomentSquare : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (ℝ → ℝ) → (ℝ → ℝ) → Fin (n+1) → ℝ → ℝ
  | 0,_,_,_,g,_ => fun x => (g x)^2
  | n+1,m,v,f,g,j => Fin.lastCases
      (scalarHierarchyAverage (n+1) m v f (fun x => (g x)^2))
      (fun i => scalarMomentSquare n (fun i => m i.castSucc) (fun i => v i.castSucc)
        (scalarStep (m (Fin.last n)) (v (Fin.last n)) f)
        (scalarStepAverage (m (Fin.last n)) (v (Fin.last n)) f g) i) j

theorem scalarParameterTerminal_const_regular (n : ℕ) (v : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    BoundedDerivs (scalarParameterTerminal n v (fun _ => f) x) :=
  (hf.translate x).compCLM (coordinateLinear n v)

theorem scalarMomentSquare_eq_hierarchyAverage (n : ℕ) (m v : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) (j : Fin (n+1)) (x a : ℝ) :
    scalarMomentSquare n m v f g j x =
      hierarchyAverage n m (scalarParameterTerminal n v (fun _ => f) x)
        (fun z => (hierarchyMomentLevel n m (scalarParameterTerminal n v (fun _ => f) x)
          (scalarParameterTerminal n v (fun _ => g) x) j z)^2) a := by
  induction n generalizing f g with
  | zero => simp [scalarMomentSquare,hierarchyAverage,hierarchyMomentLevel,
      scalarParameterTerminal,coordinateLinear]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last,hierarchyMomentLevel]
      exact (hierarchyAverage_scalarParameterTerminal (n+1) m v (fun _ => f)
        (fun _ x => (g x)^2) x a).symm
    · simp only [scalarMomentSquare,hierarchyMomentLevel,Fin.lastCases_castSucc,hierarchyAverage]
      rw [gaussianAverage_const_prefix (scalarParameterTerminal_const_regular (n+1) v hf x)
        (m (Fin.last n)) (fun z => (hierarchyMomentLevel n (fun i => m i.castSucc)
          (gaussianStep (m (Fin.last n)) (scalarParameterTerminal (n+1) v (fun _ => f) x))
          (gaussianAverage (m (Fin.last n)) (scalarParameterTerminal (n+1) v (fun _ => f) x)
            (scalarParameterTerminal (n+1) v (fun _ => g) x)) j z)^2)]
      simp only [gaussianStep_scalarParameterTerminal,gaussianAverage_scalarParameterTerminal]
      exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
        (scalarStep_regular hf _ _) _ j

end SK.Analytic

end
end

end OAI
