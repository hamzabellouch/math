import Mathlib
import OAI.Probability.LogConcave.Analysis.CenteringPotential
import OAI.Probability.LogConcave.Dynamics.JointHarmonicFlow

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal

theorem exists_conditional_harmonic_flow {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∃Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y) ∧ Ξ y 0=y) ∧
      (∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d)
          (Ξ y t)) (Icc (0:ℝ) 1) t) ∧
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) ∧
      (∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map
        (fun y => Ξ y t)=gibbs (centeringPotential F x r T)) :=
  exists_joint_harmonic_flow
    ((interpolationPotential_smooth hF x hr hl hT0 hT1).of_le (by norm_cast))
    (interpolationPotential_lowerTail hF x hr (by linarith) hT0 hT1)
    (interpolationPotential_gradient_lipschitz hF x hr hl hT0 hT1)

end LogConcaveSampling

end

end

end

end OAI
