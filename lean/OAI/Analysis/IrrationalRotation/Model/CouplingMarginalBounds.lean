import Mathlib

namespace OAI

namespace Invariant233.CouplingMarginalBounds

open MeasureTheory

noncomputable def rho (κ m w : ℝ) : ℝ := κ * Real.sqrt (w / m)

noncomputable def diagonalMass (κ m a b t : ℝ) : ℝ :=
  1 - 2 * rho κ m a - 2 * rho κ m b - t / m

noncomputable def uniformDensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Set Ω) : Ω → ℝ :=
  s.indicator (fun _ => (μ.real s)⁻¹)

noncomputable def componentProbabilities (κ m a b t : ℝ) : Fin 5 → ℝ :=
  ![rho κ m a, rho κ m a, rho κ m b, rho κ m b, t / m]

noncomputable def componentVarianceBounds (m a b : ℝ) : Fin 5 → ℝ :=
  ![2 / a, 2 / a, 2 / b, 2 / b, m]

end Invariant233.CouplingMarginalBounds

end OAI
