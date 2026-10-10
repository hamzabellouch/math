import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalSourceKernel
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedKernelWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryOuterReadCosts

namespace OAI

/-! Complete selector bounds with table and scalar-source reads. The
source-cost premises range only over the guards and cells actually visited. -/

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (old current : Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (t : ℕ) (draw : CellGroupReadDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (hb : PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S t
    tau a eta kappa delta (fun r => (parentInitial r).1)
    (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun s => (old s).1) (fun s => (current s).1) (fun s i => (history s i).1)
    (fun b r => (integer b r).1))
  (hp : ∀ r, (parentInitial r).2 ≤ R)

include hb hp in
theorem preparedLocalCellGroupsSourceWithWork_bounds (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (hn : ∀ input, (current input).2 ≤ R) (D : ℕ)
    (hd : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ D) :
    let selected := preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF
      hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N draw q
    selected.1.length ≤ (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    selected.2 ≤ preparedLocalGroupsBitBudget N M P F exponent eM eF B * tableReadFactor R * (D + 4) := by
  have hs := preparedLocalCellGroupsSourceWithWork_eq_cost_on source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N draw q D hd
  have heq := preparedLocalCellGroupsReadWithWork_eq source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N
    (fun b cell scale sample => (draw b cell scale sample).1) q hp (fun i r => hn (i, r))
  have hr := preparedLocalCellGroupsReadWithWork_factor source target parent P F exponent Q eM eF
    hM hF hP tau a parentInitial child initial (fun i r => current (i, r)) R hc hi N
    (fun b cell scale sample => (draw b cell scale sample).1) q hp (fun i r => hn (i, r))
  have hcost := preparedLocalCellGroupsWithWork_cost source target parent N P F exponent Q eM eF B hM hF hP
    tau a (fun r => (parentInitial r).1) (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun i r => (current (i, r)).1) (fun b cell scale sample => (draw b cell scale sample).1) q
    (by have := hb.largeBits; omega) hb.inputSize hb.sourceSize hb.targetSize hb.aritySize hb.sampleSize
    hb.precisionSize hb.factorSize hb.thetaSize hb.scaleSizes hb.tauSize hb.factorWidth hb.parentSize
    hb.massSize hb.initialSize (fun i r => hb.currentSize (i, r)) (hb.parentNonneg q) hPdyadic
  constructor
  · rw [hs.1, heq]
    exact preparedLocalCellGroupsWithWork_length_le source target parent N P F exponent Q eM eF B
      hM hF hP tau a (fun r => (parentInitial r).1) (fun i r => (child i r).1)
      (fun i r => (initial i r).1) (fun i r => (current (i, r)).1)
      (fun b cell scale sample => (draw b cell scale sample).1) q hb.inputSize (hb.parentNonneg q)
  · exact hs.2.trans (Nat.mul_le_mul_right (D + 4)
      (hr.trans (Nat.mul_le_mul_right (tableReadFactor R) hcost)))

include hb hp hM in
theorem preparedLocalOnlineActionsSourceWithWork_bounds
    (hh : ∀ s ≤ t + 1, ∀ input, (history s input).2 ≤ R) (D : ℕ)
    (hd : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial q).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤ D) :
    let selected := preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial history R hc hi t integer N q
    selected.1.length ≤ B + 1 ∧
    selected.2 ≤ preparedLocalOnlineBitBudget M P B S * tableReadFactor R * (D + 4) := by
  have hs := preparedLocalOnlineActionsSourceWithWork_eq_cost_on source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial history R hc hi t integer N q D hd
  have heq := preparedLocalOnlineActionsReadWithWork_eq source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial history R hc hi t (fun b r => (integer b r).1) N q hh
  have hr := preparedLocalOnlineActionsReadWithWork_factor source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial history R hc hi t (fun b r => (integer b r).1) N q hp hh
  have hcost := preparedLocalOnlineActionsWithWork_cost source target parent N P F exponent H B E S hP
    (by rw [hM]; exact Nat.two_pow_pos _) tau a eta kappa (fun r => (parentInitial r).1)
    (fun i r => (child i r).1) (fun i r => (initial i r).1) (fun s i => (history s i).1)
    t (fun b r => (integer b r).1) q (by have := hb.largeBits; omega) hb.inputSize hb.sourceSize
    hb.targetSize (by have := hb.aritySize; omega) hb.precisionSize hb.factorSize hb.thetaSize
    hb.heightSize hb.coordinateSize hb.iterationSize hb.drawSize hb.tauSize hb.factorWidth
    hb.rateSize hb.optimismSize hb.parentSize hb.massSize hb.initialSize hb.historySize hb.rateMagnitude
    hb.optimismRange hb.historyRange hb.scalePositive hb.arityCap hb.precisionCap hb.rateCap hb.timeCap
    hb.wordCap hb.actionCap hb.cartesianCap hb.iterationCap
  constructor
  · rw [hs.1, heq]
    exact preparedLocalOnlineActionsWithWork_length_le source target parent N P F exponent H B hP
      tau a eta kappa (fun r => (parentInitial r).1) (fun i r => (child i r).1)
      (fun i r => (initial i r).1) (fun s i => (history s i).1) t (fun b r => (integer b r).1) q hb.inputSize
  · exact hs.2.trans (Nat.mul_le_mul_right (D + 4)
      (hr.trans (Nat.mul_le_mul_right (tableReadFactor R) hcost)))

end Selectors
end EditApproximation.BinaryFraction

end OAI
