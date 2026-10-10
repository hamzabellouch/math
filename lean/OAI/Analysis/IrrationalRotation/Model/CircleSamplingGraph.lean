import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.CircleParameterData

def samplingDensity (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (endpoint : Bool) (x : Circle) : ℝ :=
  ∏ i ∈ p.block j, orientedKernel endpoint (p.m j) (p.coordinate i x)
    (Int.fract ((n : ℝ) * p.alpha θ i))

def samplingTranslation (θ : ℝ) (n : ℕ) (x : Circle) : Circle :=
  x + (((n : ℝ) * θ : ℝ) : Circle)

def samplingGraph (p : CircleParameterData) (θ : ℝ) (j n : ℕ) :
    Measure (Circle × Circle) :=
  (circleMeasure.withDensity
    (fun x => ENNReal.ofReal (p.samplingDensity θ j n false x))).map
      (fun x => (x, samplingTranslation θ n x))

def samplingGraphAverage (p : CircleParameterData) (θ : ℝ) (j r : ℕ) :
    Measure (Circle × Circle) :=
  ENNReal.ofReal (1 / ((p.samples j r).card : ℝ)) •
    ∑ n ∈ p.samples j r, p.samplingGraph θ j n

end Invariant233.CircleParameterData

end

end OAI
