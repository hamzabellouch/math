import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.TrialSampling

def phaseLaw (m : ℕ) (N : ℝ) : Measure (Fin m → ℝ) :=
  Measure.infinitePi (fun _ : Fin m =>
    ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N)))

def spatialLaw (m : ℕ) : Measure (Fin m → Circle) :=
  Measure.pi (fun _ : Fin m => circleMeasure)

def average (m : ℕ) (samples : Finset ℕ) (endpoint : Bool)
    (phase : Fin m → ℝ) (z : Fin m → Circle) : ℝ :=
  (samples.card : ℝ)⁻¹ * ∑ n ∈ samples, ∏ i : Fin m,
    CircleParameterData.orientedKernel endpoint m
      (CircleParameterData.rep (z i)) (Int.fract ((n : ℝ) * phase i))

def squaredError (m : ℕ) (samples : Finset ℕ) (endpoint : Bool)
    (phase : Fin m → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((average m samples endpoint phase z - 1) ^ 2) ∂spatialLaw m

def pairLaw (N : ℝ) : Measure (ℝ × Circle) :=
  (ProbabilityTheory.cond volume (Set.Icc (1 / N) (2 / N))).prod circleMeasure

def coordinateSample (m : ℕ) (endpoint : Bool) (n : ℕ) (p : ℝ × Circle) : ℝ :=
  CircleParameterData.orientedKernel endpoint m (CircleParameterData.rep p.2)
    (Int.fract ((n : ℝ) * p.1))

def coordinateIdeal (m : ℕ) (endpoint : Bool) (p : ℝ × Circle) : ℝ :=
  ∫ v, CircleParameterData.orientedKernel endpoint m (CircleParameterData.rep p.2) v
    ∂volume.restrict (Set.Ioc (0 : ℝ) 1)

end Invariant233.TrialSampling

end

end OAI
