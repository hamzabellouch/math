import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OAI

namespace Ostmann

noncomputable def normalizedExpSum (s : Finset ℕ) (t : ℝ) : ℂ :=
  (∑ n ∈ s, Complex.exp (2 * Real.pi * Complex.I * n * t)) / (s.card : ℂ)

end Ostmann

end OAI
