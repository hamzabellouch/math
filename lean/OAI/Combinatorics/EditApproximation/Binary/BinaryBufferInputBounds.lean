import OAI.Combinatorics.EditApproximation.Refinement.PhysicalPreparedInputBounds
import OAI.Combinatorics.EditApproximation.Geometry.RefinementBufferRanges

namespace OAI

/-! A refinement continuation has a separate current-index buffer.
Only the earlier-history buffer enters the online objective, so its
range invariant does not require any relation at unused current keys. -/

namespace EditApproximation
namespace BinaryFraction

theorem PreparedKernelNumericBounds.with_independent_cached_values {nx ny M : ℕ}
    {N P F exponent H Q eM eF B E S t : ℕ}
    {tau a eta kappa delta : BinaryFraction}
    {integer : ℕ → TargetInterval ny → ℕ}
    (hn : PreparedKernelNumericBounds (nx := nx) (M := M)
      N P F exponent H Q eM eF B E S t tau a eta kappa delta integer)
    (parentInitial : TargetInterval ny → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval ny → BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (hp : ∀ r, (parentInitial r).width ≤ B)
    (hm : ∀ i r, (childMass i r).width ≤ B)
    (hi : ∀ i r, (childInitial i r).width ≤ B)
    (ho : ∀ input, (old input).width ≤ B)
    (hc : ∀ input, (current input).width ≤ B)
    (hh : ∀ s ≤ t + 1, ∀ i r, (history s (i, r)).width ≤ B)
    (hpnonneg : ∀ r, 0 ≤ (parentInitial r).value)
    (hrange : ∀ s ≤ t + 1, ∀ i r, 0 ≤ (history s (i, r)).value ∧
      (history s (i, r)).value ≤ (childInitial i r).value) :
    PreparedKernelInputBounds (nx := nx) N P F exponent H Q eM eF B E S t
      tau a eta kappa delta parentInitial childMass childInitial old current history integer := by
  exact { (hn.with_cached_values parentInitial childMass childInitial history
    hp hm hi hh hpnonneg hrange) with oldSize := ho, currentSize := hc }

end BinaryFraction
end EditApproximation

end OAI
