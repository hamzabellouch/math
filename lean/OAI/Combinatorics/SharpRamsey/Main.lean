import Mathlib
import OAI.Combinatorics.SharpRamsey.Construction.PrimeConstruction
import OAI.Combinatorics.SharpRamsey.Bounds.FromConstruction

namespace OAI

/-! Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers. -/

section
namespace SharpLogRamsey

theorem main (s : ℕ) (hs : 6 ≤ s) : MainBounds s ∧ MainLimit s :=
  main_of_primeConstruction s hs (LowerTransfer.prime_construction (s-1) (by omega))
end SharpLogRamsey

end

end OAI
