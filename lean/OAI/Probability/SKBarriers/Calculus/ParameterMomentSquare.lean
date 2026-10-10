import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMomentSquare

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarMomentSquare_eq_parameterAverage (n : ℕ) (m v : Fin n → ℝ)
    (F H : ℝ → ℝ → ℝ) (x a : ℝ)
    (hf : BoundedDerivs (scalarParameterTerminal n v F x)) (j : Fin (n+1)) :
    scalarMomentSquare n m v (F a) (H a) j x =
      hierarchyAverage n m (scalarParameterTerminal n v F x)
        (fun z => (hierarchyMomentLevel n m (scalarParameterTerminal n v F x)
          (scalarParameterTerminal n v H x) j z)^2) a := by
  induction n generalizing F H with
  | zero => simp [scalarMomentSquare,hierarchyAverage,hierarchyMomentLevel,
      scalarParameterTerminal,coordinateLinear,parameter]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last,hierarchyMomentLevel]
      exact (hierarchyAverage_scalarParameterTerminal (n+1) m v F
        (fun a x => (H a x)^2) x a).symm
    · simp only [scalarMomentSquare,hierarchyMomentLevel,Fin.lastCases_castSucc,hierarchyAverage]
      rw [gaussianAverage_const_prefix hf (m (Fin.last n)) (fun z =>
        (hierarchyMomentLevel n (fun i => m i.castSucc)
          (gaussianStep (m (Fin.last n)) (scalarParameterTerminal (n+1) v F x))
          (gaussianAverage (m (Fin.last n)) (scalarParameterTerminal (n+1) v F x)
            (scalarParameterTerminal (n+1) v H x)) j z)^2)]
      simp only [gaussianStep_scalarParameterTerminal,gaussianAverage_scalarParameterTerminal]
      have hf' := hf.gaussianStep (m (Fin.last n))
      rw [gaussianStep_scalarParameterTerminal] at hf'
      exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
        (fun a => scalarStep (m (Fin.last n)) (v (Fin.last n)) (F a))
        (fun a => scalarStepAverage (m (Fin.last n)) (v (Fin.last n)) (F a) (H a)) hf' j

end SK.Analytic

end
end

end OAI
