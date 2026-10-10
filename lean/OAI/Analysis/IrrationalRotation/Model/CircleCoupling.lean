import OAI.Analysis.IrrationalRotation.Model.CircleDigitCoupling
import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Model.MixedRadixCircle
import Mathlib.Probability.ProductMeasure

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

abbrev Sample := ℕ → CoordinateSample

def initialLaw : Measure CoordinateSample :=
  baseLaw.map (fun x => (none, (x, x)))

def tag (j s : ℕ) : ℝ := if s = j then 1 else 0

def coordinateLaw (p : CircleParameterData) (j i : ℕ) : Measure CoordinateSample :=
  if i = 0 then initialLaw else
    rawLaw (kappa (p.blockIndex i)) (p.m (p.blockIndex i))
      (p.a (p.blockIndex i)) (p.b (p.blockIndex i)) (tag j (p.blockIndex i))

def law (p : CircleParameterData) (j : ℕ) : Measure Sample :=
  Measure.infinitePi (coordinateLaw p j)

def observedDigit (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (i : ℕ) (z : CoordinateSample) : Fin (MixedRadix.radices p.q i) := by
  letI : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  exact UniformQuantization.quantize (MixedRadix.radices p.q i) (endpoint side z)

def digits (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) : MixedRadix.Digits (MixedRadix.radices p.q) :=
  fun i => observedDigit p hr side i (ω i)

def point (p : CircleParameterData) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (side : Bool) (ω : Sample) : Circle := MixedRadix.circleValue (digits p hr side ω)

def label (i : ℕ) (ω : Sample) : Label := (ω i).1

def posterior (p : CircleParameterData) (j : ℕ) (side : Bool) (i : ℕ) :
    Kernel (Fin (MixedRadix.radices p.q i)) Label :=
  if i = 0 then Kernel.const _ (Measure.dirac none) else
    labelsGivenDigit side (MixedRadix.radices p.q i) (kappa (p.blockIndex i))
      (p.m (p.blockIndex i)) (p.a (p.blockIndex i)) (p.b (p.blockIndex i))
      (tag j (p.blockIndex i))

end Invariant233.CircleCoupling

end

end OAI
