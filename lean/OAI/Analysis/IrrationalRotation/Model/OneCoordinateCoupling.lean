import OAI.Analysis.IrrationalRotation.Model.CouplingMarginalBounds
import OAI.Analysis.IrrationalRotation.Model.CouplingMixture

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

noncomputable def baseLaw : Measure ℝ := intervalLaw 0 1

noncomputable def leftLaw (m a b : ℝ) : Fin 5 → Measure ℝ :=
  ![intervalLaw 0 (1 - a / 2), intervalLaw 0 (a / 2),
    intervalLaw 0 (1 - b / 2), intervalLaw 0 (b / 2), intervalLaw 0 (1 / m)]

noncomputable def rightLaw (m a b : ℝ) : Fin 5 → Measure ℝ :=
  ![intervalLaw (1 - a / 2) 1, intervalLaw (a / 2) 1,
    intervalLaw (1 - b / 2) 1, intervalLaw (b / 2) 1, intervalLaw (1 - 1 / m) 1]

noncomputable def pairLaw (κ m a b t : ℝ) : Measure (ℝ × ℝ) :=
  mixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (leftLaw m a b) (rightLaw m a b)

instance labelMeasurableSpace : MeasurableSpace (Option (Fin 5)) := ⊤

instance labelMeasurableSingletonClass : MeasurableSingletonClass (Option (Fin 5)) :=
  ⟨fun _ => trivial⟩

noncomputable def labelledLaw (κ m a b t : ℝ) :
    Measure (Option (Fin 5) × (ℝ × ℝ)) :=
  labelledMixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (leftLaw m a b) (rightLaw m a b)

noncomputable def intervalDensity (a b : ℝ) : ℝ → ℝ :=
  uniformDensity baseLaw (Set.Ico a b)

noncomputable def leftDensity (m a b : ℝ) : Fin 5 → ℝ → ℝ :=
  ![intervalDensity 0 (1 - a / 2), intervalDensity 0 (a / 2),
    intervalDensity 0 (1 - b / 2), intervalDensity 0 (b / 2), intervalDensity 0 (1 / m)]

noncomputable def rightDensity (m a b : ℝ) : Fin 5 → ℝ → ℝ :=
  ![intervalDensity (1 - a / 2) 1, intervalDensity (a / 2) 1,
    intervalDensity (1 - b / 2) 1, intervalDensity (b / 2) 1,
    intervalDensity (1 - 1 / m) 1]

noncomputable def leftMarginalDensity (κ m a b t x : ℝ) : ℝ :=
  diagonalMass κ m a b t +
    ∑ i, componentProbabilities κ m a b t i * leftDensity m a b i x

noncomputable def rightMarginalDensity (κ m a b t x : ℝ) : ℝ :=
  diagonalMass κ m a b t +
    ∑ i, componentProbabilities κ m a b t i * rightDensity m a b i x

end Invariant233.OneCoordinateCoupling

end OAI
