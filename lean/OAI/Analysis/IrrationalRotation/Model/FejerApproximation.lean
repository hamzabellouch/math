import OAI.Analysis.IrrationalRotation.Model.Fejer

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Fejer

def approximation (H : ℕ) (f : Circle → ℝ) (x : Circle) : ℝ :=
  ∫ y, kernel H (x - y) * f y

def approximationCoefficient (H : ℕ) (f : Circle → ℝ) (v : ℤ) : ℂ :=
  coefficient H v * ∫ y, fourier (-v) y * (f y : ℂ)

end Invariant233.Fejer

end

end OAI
