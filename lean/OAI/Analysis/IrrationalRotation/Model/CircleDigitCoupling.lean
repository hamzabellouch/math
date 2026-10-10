import OAI.Analysis.IrrationalRotation.Model.OneCoordinateCoupling
import OAI.Analysis.IrrationalRotation.Model.FiniteKernelMixture
import OAI.Analysis.IrrationalRotation.Model.UniformQuantization

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

abbrev Label := Option (Fin 5)
abbrev CoordinateSample := Label × (ℝ × ℝ)

def endpointLaw (side : Bool) (m a b : ℝ) : Label → Measure ℝ
  | none => baseLaw
  | some i => if side then rightLaw (2 * m) a b i else leftLaw (2 * m) a b i

def endpointDensity (side : Bool) (m a b : ℝ) : Label → ℝ → ℝ
  | none => fun _ => 1
  | some i => if side then rightDensity (2 * m) a b i else leftDensity (2 * m) a b i

def marginalDensity (side : Bool) (κ m a b t x : ℝ) : ℝ :=
  diagonalMass κ m a b t +
    ∑ i, componentProbabilities κ m a b t i * endpointDensity side m a b (some i) x

def labelMass (κ m a b t : ℝ) : Label → ℝ≥0∞
  | none => ENNReal.ofReal (diagonalMass κ m a b t)
  | some i => ENNReal.ofReal (componentProbabilities κ m a b t i)

def rawLaw (κ m a b t : ℝ) : Measure CoordinateSample :=
  labelledMixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
    (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
    (leftLaw (2 * m) a b) (rightLaw (2 * m) a b)

def endpoint (side : Bool) (z : CoordinateSample) : ℝ :=
  if side then z.2.2 else z.2.1

def bin (r : ℕ) (d : Fin r) : Set ℝ :=
  Set.Ico ((d : ℝ) / r) (((d : ℝ) + 1) / r)

def digitJoint (side : Bool) (r : ℕ) [NeZero r] (κ m a b t : ℝ) :
    Measure (Fin r × Label) :=
  (rawLaw κ m a b t).map (fun z =>
    (UniformQuantization.quantize r (endpoint side z), z.1))

def digitWeight (side : Bool) (r : ℕ) (κ m a b t : ℝ)
    (l : Label) (d : Fin r) : ℝ≥0∞ :=
  labelMass κ m a b t l * endpointLaw side m a b l (bin r d)

def labelsGivenDigit (side : Bool) (r : ℕ) (κ m a b t : ℝ) : Kernel (Fin r) Label :=
  FiniteKernelMixture.normalizedKernel
    (fun l => Kernel.const (Fin r) (Measure.dirac l))
    (digitWeight side r κ m a b t)
    (fun _ => measurable_of_countable _)

def width (a b : ℝ) (which : Bool) : ℝ := if which then b else a

def topLabel (which : Bool) : Label := some (if which then 2 else 0)
def bottomLabel (which : Bool) : Label := some (if which then 3 else 1)

end Invariant233.CircleDigitCoupling

end

end OAI
