import OAI.Combinatorics.EditApproximation.Queries.QueryLocalSelectors

namespace OAI

/-! Read budgets certify fixed buffer algorithms. Enlarging the
budget changes proof arguments only, and preserves both values and work. -/

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R R' : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (hc' : ∀ i r, (child i r).2 ≤ R') (hi' : ∀ i r, (initial i r).2 ≤ R')

theorem queryGroupSelectWithWork_readBound_irrel (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R hc hi draw keys words q =
    queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R' hc' hi' draw keys words q := by
  rfl

theorem queryOnlineSelectWithWork_readBound_irrel (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer keys words q =
    queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R' hc' hi' t integer keys words q := by
  rfl

end Selectors
end EditApproximation.BinaryFraction

end OAI
