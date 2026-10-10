import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

noncomputable section

namespace Invariant233.ScalarSampling

def delta (s : ℝ) : ℝ := min s (1 - s)

def rawKernel (h α s t : ℝ) : ℝ :=
  if α ≤ delta s then
    (Set.Ioo 0 (h * delta s)).indicator (fun _ => (h * delta s)⁻¹) t
  else 0

def circleKernel (h α z v : ℝ) : ℝ :=
  rawKernel h α (Int.fract z) (Int.fract v)

def manuscriptKernel (m : ℕ) (z v : ℝ) : ℝ :=
  circleKernel ((m : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) z v

def manuscriptEndpointKernel (m : ℕ) (z v : ℝ) : ℝ :=
  manuscriptKernel m (z - v) v

def triangularKernel (s t : ℝ) : ℝ :=
  (Set.Ioo 0 (1 - s)).indicator (fun _ => 1) t

end Invariant233.ScalarSampling

end

end OAI
