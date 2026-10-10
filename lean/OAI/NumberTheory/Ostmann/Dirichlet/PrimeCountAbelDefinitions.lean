import Mathlib

namespace OAI

namespace Ostmann.Dirichlet.PrimeCountAbel
open MeasureTheory

noncomputable def logarithmicIntegral (x : ℝ) : ℝ := ∫ t in 2..x, 1 / Real.log t

end Ostmann.Dirichlet.PrimeCountAbel

end OAI
