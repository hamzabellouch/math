import OAI.Analysis.IrrationalRotation.Model.MixedRadix
import Mathlib.MeasureTheory.Group.AddCircle

namespace OAI

namespace Invariant233.MixedRadix

noncomputable def circleValue {r : ℕ → ℕ} (d : Digits r) : AddCircle (1 : ℝ) :=
  (ofDigits d : AddCircle (1 : ℝ))

noncomputable def circleCanonical (r : ℕ → ℕ) (hr : ∀ n, 0 < r n)
    (x : AddCircle (1 : ℝ)) : Digits r :=
  canonicalDigits r hr (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

end Invariant233.MixedRadix

end OAI
