import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.ProductMeasure

namespace OAI

noncomputable section

open MeasureTheory

namespace Invariant233.ProductCocycle

abbrev Space (I : Type*) := I → UnitAddCircle

def haar (I : Type*) : Measure (Space I) :=
  Measure.infinitePi (fun _ : I ↦ (volume : Measure UnitAddCircle))

def representative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

def rotate {I : Type*} (θ : I → ℝ) (k : ℤ) (x : Space I) : Space I :=
  fun i ↦ x i + (((k : ℝ) * θ i : ℝ) : UnitAddCircle)

def cocycleVersion {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) : ℝ :=
  Real.exp (-(∑' i, c i * (⌊representative (x i) + (k : ℝ) * θ i⌋ : ℝ)))

end Invariant233.ProductCocycle

end

end OAI
