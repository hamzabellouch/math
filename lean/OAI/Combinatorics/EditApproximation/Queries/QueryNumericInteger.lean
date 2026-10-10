import OAI.Combinatorics.EditApproximation.Refinement.PhysicalPreparedInputBounds

namespace OAI

namespace EditApproximation.BinaryFraction

/-- Changing the sampled integers changes only their explicit width premise. -/
theorem PreparedKernelNumericBounds.with_integer {nx ny M : ℕ}
    {N P F exponent H Q eM eF B E S t : ℕ}
    {tau a eta kappa delta : BinaryFraction} {integer : ℕ → TargetInterval ny → ℕ}
    (hn : PreparedKernelNumericBounds (nx := nx) (M := M)
      N P F exponent H Q eM eF B E S t tau a eta kappa delta integer)
    (integer' : ℕ → TargetInterval ny → ℕ) (hi : ∀ b r, Nat.size (integer' b r) ≤ B) :
    PreparedKernelNumericBounds (nx := nx) (M := M)
      N P F exponent H Q eM eF B E S t tau a eta kappa delta integer' := by
  exact { hn with drawSize := hi }

end EditApproximation.BinaryFraction

end OAI
