import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalAdmissibility
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyLocalConstruction
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildConservation
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildConservation

namespace OAI

/-! # All local admissibility properties for the same actual mild solution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.MildCollisionSolution

theorem localAdmissible {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p) (hf₀ : FiniteEntropyDatum f₀)
    (hfinite : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (positiveEvolution T f₀ g t))
    (hH : ∀ t ∈ Icc 0 T,
      ENNReal.ofReal (relativeEntropy (positiveEvolution T f₀ g t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (positiveEvolution T f₀ g s)) ≤
        ENNReal.ofReal (relativeEntropy f₀))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    AdmissibleLocal T f₀ (positiveEvolution T f₀ g) := by
  have hM := uniform_entropyMoment_of_entropy_inequality hf₀ hfinite hH
  have hEi := entropyMoment_spacetime_integrable (S.positiveEvolution_measurable hf₀m)
    positiveEvolution_nonnegative hfinite hM
  refine ⟨S.localMildSolution hT hf₀m hf₀.integrable hf₀n,hf₀,hfinite,hM,
    S.positiveEvolution_collision_fibers hf₀m,S.renormalized_integrable hf₀m,?_,?_,?_,?_,?_,hH⟩
  · intro β φ
    rw [S.renormalized_balance hT hf₀m hf₀.integrable hf₀n β φ]
    ring
  · intro φ
    change Integrable _ _
    rw [← phaseInterval_measure]
    exact mass_transport_integrable (S.positiveEvolution_measurable hf₀m) positiveEvolution_nonnegative hEi φ
  · intro φ
    rw [S.local_mass_balance hT hf₀m hf₀.integrable hEi φ]
    ring
  · exact fun _ ht => S.momentum_conservation hT hf₀m hf₀ hfinite hE ht
  · exact fun _ ht => S.energy_conservation hT hf₀m hf₀.integrable hf₀.integrable_energy hE ht

end BoltzmannNonuniqueness.MildCollisionSolution

end

end OAI
