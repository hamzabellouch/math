import OAI.Analysis.IrrationalRotation.Model.MixedRadix
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

namespace OAI

noncomputable section

open MeasureTheory

namespace Invariant233.MixedRadix

def digitLaw (r : ℕ → ℕ) (hr : ∀ n, 0 < r n) : Measure (Digits r) := by
  letI : ∀ n, NeZero (r n) := fun n => ⟨ne_of_gt (hr n)⟩
  exact Measure.infinitePi (fun n => (PMF.uniformOfFintype (Fin (r n))).toMeasure)

end Invariant233.MixedRadix

end

end OAI
