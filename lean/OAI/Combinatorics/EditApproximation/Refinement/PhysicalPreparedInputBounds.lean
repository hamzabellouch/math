import OAI.Combinatorics.EditApproximation.Refinement.PhysicalBinaryStep
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalBinaryMass

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Numeric register and loop bounds, independent of previously cached values. -/
structure PreparedKernelNumericBounds {nx ny M : ℕ}
    (N P F exponent H Q eM eF B E S t : ℕ)
    (tau a eta kappa delta : BinaryFraction)
    (integer : ℕ → TargetInterval ny → ℕ) : Prop where
  largeBits : 10 ≤ B
  inputSize : Nat.size N ≤ B
  sourceSize : Nat.size nx + 2 ≤ B
  targetSize : Nat.size ny + 2 ≤ B
  aritySize : Nat.size M + 2 ≤ B
  precisionSize : Nat.size P ≤ B
  factorSize : Nat.size F + 2 ≤ B
  sampleSize : Nat.size Q + 2 ≤ B
  thetaSize : exponent + 1 ≤ B
  scaleSizes : eM + eF + 7 ≤ B
  heightSize : Nat.size H ≤ B
  coordinateSize : Nat.size (M * (40 * P + 2) ^ 2) ≤ B
  iterationSize : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ B
  drawSize : ∀ b r, Nat.size (integer b r) ≤ B
  tauSize : tau.width ≤ B
  factorWidth : a.width ≤ B
  rateSize : eta.width ≤ B
  optimismSize : kappa.width ≤ B
  decrementSize : delta.width ≤ B
  rateMagnitude : |eta.value| ≤ E
  optimismRange : 0 ≤ kappa.value ∧ kappa.value ≤ 1
  scalePositive : 2 ≤ S
  arityCap : M ≤ S
  precisionCap : P ≤ S
  rateCap : E ≤ S
  timeCap : t ≤ S
  wordCap : 3 * (B + 4) + 4 ≤ S
  actionCap : (40 * P + 2) ^ (2 * M) ≤ S
  cartesianCap : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S
  iterationCap : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S

theorem PreparedKernelNumericBounds.with_cached_values {nx ny M : ℕ}
    {N P F exponent H Q eM eF B E S t : ℕ}
    {tau a eta kappa delta : BinaryFraction}
    {integer : ℕ → TargetInterval ny → ℕ}
    (hn : PreparedKernelNumericBounds (nx := nx) (M := M)
      N P F exponent H Q eM eF B E S t tau a eta kappa delta integer)
    (parentInitial : TargetInterval ny → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval ny → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (hp : ∀ r, (parentInitial r).width ≤ B)
    (hm : ∀ i r, (childMass i r).width ≤ B)
    (hi : ∀ i r, (childInitial i r).width ≤ B)
    (hh : ∀ s ≤ t + 1, ∀ i r, (history s (i, r)).width ≤ B)
    (hpnonneg : ∀ r, 0 ≤ (parentInitial r).value)
    (hrange : ∀ s ≤ t + 1, ∀ i r, 0 ≤ (history s (i, r)).value ∧
      (history s (i, r)).value ≤ (childInitial i r).value) :
    PreparedKernelInputBounds (nx := nx) N P F exponent H Q eM eF B E S t
      tau a eta kappa delta parentInitial childMass childInitial
      (history t) (history (t + 1)) history integer where
  largeBits := hn.largeBits
  inputSize := hn.inputSize
  sourceSize := hn.sourceSize
  targetSize := hn.targetSize
  aritySize := hn.aritySize
  precisionSize := hn.precisionSize
  factorSize := hn.factorSize
  sampleSize := hn.sampleSize
  thetaSize := hn.thetaSize
  scaleSizes := hn.scaleSizes
  heightSize := hn.heightSize
  coordinateSize := hn.coordinateSize
  iterationSize := hn.iterationSize
  drawSize := hn.drawSize
  tauSize := hn.tauSize
  factorWidth := hn.factorWidth
  rateSize := hn.rateSize
  optimismSize := hn.optimismSize
  decrementSize := hn.decrementSize
  parentSize := hp
  massSize := hm
  initialSize := hi
  oldSize := fun s => hh t (Nat.le_succ _) s.1 s.2
  currentSize := fun s => hh (t + 1) le_rfl s.1 s.2
  historySize := hh
  parentNonneg := hpnonneg
  rateMagnitude := hn.rateMagnitude
  optimismRange := hn.optimismRange
  historyRange := hrange
  scalePositive := hn.scalePositive
  arityCap := hn.arityCap
  precisionCap := hn.precisionCap
  rateCap := hn.rateCap
  timeCap := hn.timeCap
  wordCap := hn.wordCap
  actionCap := hn.actionCap
  cartesianCap := hn.cartesianCap
  iterationCap := hn.iterationCap

end BinaryFraction

/-- The actual all-seed physical invariants discharge the value premises
of the prepared evaluator; only representation and scalar register bounds remain. -/
theorem physicalPreparedStep_inputBounds {α : Type*} [DecidableEq α]
    {M J R : ℕ} [NeZero R] (source target : List α)
    (N P F exponent H Q eM eF B E S : ℕ)
    (tauWord aWord etaWord kappaWord deltaWord : BinaryFraction)
    (parentWords : TargetInterval target.length → BinaryFraction)
    (massWords initialWords : Fin M → TargetInterval target.length → BinaryFraction)
    (historyWords : ℕ → Fin M × TargetInterval target.length → BinaryFraction)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (integer : PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (t : ℕ)
    (U : PhysicalEntry M J target.length → ℕ) (A tau eta kappa delta : ℚ) (T : ℕ)
    (hd : 0 ≤ delta)
    (hparent : ∀ r, (parentWords r).value = stageInitial source target U N P F A (node, r))
    (hinitial : ∀ i r, (initialWords i r).value =
      stageInitial source target U N P F A (physicalChild node hbelow i, r))
    (hhistory : ∀ s i r, (historyWords s (i, r)).value =
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw
        (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
        (physicalChild node hbelow i) s r)
    (hn : BinaryFraction.PreparedKernelNumericBounds (nx := source.length) (M := M)
      N P F exponent H Q eM eF B E S t tauWord aWord etaWord kappaWord deltaWord
      (integer ⟨node, hbelow⟩ (Fin.ofNat R t)))
    (hp : ∀ r, (parentWords r).width ≤ B)
    (hm : ∀ i r, (massWords i r).width ≤ B)
    (hi : ∀ i r, (initialWords i r).width ≤ B)
    (hh : ∀ s ≤ t + 1, ∀ i r, (historyWords s (i, r)).width ≤ B) :
    BinaryFraction.PreparedKernelInputBounds (nx := source.length)
      N P F exponent H Q eM eF B E S t tauWord aWord etaWord kappaWord deltaWord
      parentWords massWords initialWords (historyWords t) (historyWords (t + 1)) historyWords
      (integer ⟨node, hbelow⟩ (Fin.ofNat R t)) := by
  apply hn.with_cached_values parentWords massWords initialWords historyWords hp hm hi hh
  · intro r
    rw [hparent]
    exact stageInitial_nonneg_all_seeds source target U N P F A (node, r)
  · intro s _hs i r
    rw [hhistory, hinitial]
    exact physicalLocalRefinement_bounds source target U N P F exponent Q A tau delta T hd draw
      (physicalLocalOnline source target U N P F exponent H T A tau eta kappa integer)
      (physicalChild node hbelow i) s r

end EditApproximation

end OAI
