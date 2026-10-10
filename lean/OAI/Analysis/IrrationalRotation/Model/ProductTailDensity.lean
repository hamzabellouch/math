import OAI.Analysis.IrrationalRotation.Model.ProductBase
import OAI.Analysis.IrrationalRotation.Model.BiasedTailDensity

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

abbrev Prefix (D : ℕ) := {i : ℕ // i < D} → Circle
abbrev Tail (D : ℕ) := {i : ℕ // ¬i < D} → Circle

def prefixMeasure (D : ℕ) : Measure (Prefix D) :=
  Measure.infinitePi fun _ : {i : ℕ // i < D} => circleMeasure

def tailMeasure (D : ℕ) : Measure (Tail D) :=
  Measure.infinitePi fun _ : {i : ℕ // ¬i < D} => circleMeasure

def splitCoordinates (D : ℕ) : Base ≃ᵐ Prefix D × Tail D :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ℕ => Circle) (fun i => i < D)

def tailCoordinates (D : ℕ) (x : Base) : Tail D := fun i => x i

def prefixTailDensity (D : ℕ) (g : Base → ℝ) : Tail D → ℝ :=
  BiasedTailDensity.tailDensity (prefixMeasure D) (g ∘ (splitCoordinates D).symm)

end Invariant233.ProductModel

end

end OAI
