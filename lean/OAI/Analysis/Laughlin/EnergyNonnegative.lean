import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import OAI.Analysis.Laughlin.Model

namespace OAI

namespace Laughlin

theorem energy_nonneg {N Q : ℕ} (ψ : State N Q) : 0 ≤ energy ψ := by
  unfold energy
  positivity

end Laughlin

end OAI
