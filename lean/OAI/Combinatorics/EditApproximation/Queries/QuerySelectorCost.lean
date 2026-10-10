import OAI.Combinatorics.EditApproximation.Binary.BinarySourceSelectorBounds
import OAI.Combinatorics.EditApproximation.Queries.QueryReadBoundIrrelevance

namespace OAI

/-! Selector bounds for the actual separate history and shared-current
buffers. The original child-reader budget is preserved in the program. -/

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R U : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (hcU : ∀ i r, (child i r).2 ≤ U) (hiU : ∀ i r, (initial i r).2 ≤ U)
  (hp : ∀ r, (parentInitial r).2 ≤ U)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) (earlierWords : List BinaryFraction)
  (sharedKeys : List (Fin M × TargetInterval target.length)) (sharedWords : List BinaryFraction)
  (q : TargetInterval target.length)
  (hb : PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
    tau a eta kappa delta (fun r => (parentInitial r).1)
    (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun input => (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).1)
    (fun input => (queryChildReadWithWork sharedKeys sharedWords input.1 input.2).1)
    (fun s input => (queryHistoryReadWithWork earlierKeys earlierWords s input).1)
    (fun b r => (integer b r).1))

include hb hp hcU hiU in
theorem queryGroupSelectWithWork_bounds (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (hshared : ∀ i r, (queryChildReadWithWork sharedKeys sharedWords i r).2 ≤ U) (D : ℕ)
    (hd : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ D) :
    let selected := queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
      tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q
    selected.1.length ≤ (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    selected.2 ≤ preparedLocalGroupsBitBudget N M P F exponent eM eF B * tableReadFactor U * (D + 4) := by
  have h := preparedLocalCellGroupsSourceWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM hF tau a eta kappa delta parentInitial child initial
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadWithWork sharedKeys sharedWords input.1 input.2)
    (queryHistoryReadWithWork earlierKeys earlierWords) U hcU hiU (t - 1) draw integer q hb hp hPdyadic
    (fun input => hshared input.1 input.2) D hd
  rw [queryGroupSelectWithWork_readBound_irrel source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R U hc hi hcU hiU draw sharedKeys sharedWords q]
  simpa only [queryGroupSelectWithWork] using h

include hb hp hcU hiU hM in
theorem queryOnlineSelectWithWork_bounds
    (hh : ∀ s ≤ t - 1 + 1, ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords s input).2 ≤ U)
    (D : ℕ)
    (hd : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial q).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤ D) :
    let selected := queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer earlierKeys earlierWords q
    selected.1.length ≤ B + 1 ∧
    selected.2 ≤ preparedLocalOnlineBitBudget M P B S * tableReadFactor U * (D + 4) := by
  have h := preparedLocalOnlineActionsSourceWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM tau a eta kappa delta parentInitial child initial
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadWithWork sharedKeys sharedWords input.1 input.2)
    (queryHistoryReadWithWork earlierKeys earlierWords) U hcU hiU (t - 1) integer q hb hp hh D hd
  rw [queryOnlineSelectWithWork_readBound_irrel source target parent N P F exponent H hP
    tau a eta kappa parentInitial child initial R U hc hi hcU hiU t integer earlierKeys earlierWords q]
  simpa only [queryOnlineSelectWithWork] using h

end Selectors
end EditApproximation.BinaryFraction

end OAI
