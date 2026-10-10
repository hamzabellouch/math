import OAI.Combinatorics.EditApproximation.Binary.BinaryPhysicalContinuationWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalOnlineWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalGroupWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedListBounds

namespace OAI

/-! The complete prepared refinement kernel has a single arithmetic bound.
All generated grids, guards, selected actions and the returned value are
charged. The premises below describe only stored input words and numeric
parameters; action geometry and output-list bounds are derived. -/

namespace EditApproximation
namespace BinaryFraction

structure PreparedKernelInputBounds {nx ny M : ℕ}
    (N P F exponent H Q eM eF B E S t : ℕ)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval ny → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval ny → BinaryFraction)
    (old current : Fin M × TargetInterval ny → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval ny → BinaryFraction)
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
  parentSize : ∀ r, (parentInitial r).width ≤ B
  massSize : ∀ i r, (childMass i r).width ≤ B
  initialSize : ∀ i r, (childInitial i r).width ≤ B
  oldSize : ∀ s, (old s).width ≤ B
  currentSize : ∀ s, (current s).width ≤ B
  historySize : ∀ s ≤ t + 1, ∀ i r, (history s (i, r)).width ≤ B
  parentNonneg : ∀ r, 0 ≤ (parentInitial r).value
  rateMagnitude : |eta.value| ≤ E
  optimismRange : 0 ≤ kappa.value ∧ kappa.value ≤ 1
  historyRange : ∀ s ≤ t + 1, ∀ i r, 0 ≤ (history s (i, r)).value ∧
    (history s (i, r)).value ≤ (childInitial i r).value
  scalePositive : 2 ≤ S
  arityCap : M ≤ S
  precisionCap : P ≤ S
  rateCap : E ≤ S
  timeCap : t ≤ S
  wordCap : 3 * (B + 4) + 4 ≤ S
  actionCap : (40 * P + 2) ^ (2 * M) ≤ S
  cartesianCap : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S
  iterationCap : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ S

def preparedKernelBitBudget (N M P F exponent eM eF B S : ℕ) : ℕ :=
  localRepresentativesBitBudget P F B + preparedLocalGroupsBitBudget N M P F exponent eM eF B +
    preparedLocalOnlineBitBudget M P B S +
    physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2)
      ((B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2) (B + 1) (B + 4) + 4

def preparedKernelWordBudget (M B : ℕ) : ℕ :=
  localContinuationWordBudget M (physicalContinuationInputBudget M (B + 4))

private theorem physicalContinuationBitBudget_mono_counts (M P nr ng no nr' ng' no' B : ℕ)
    (hr : nr ≤ nr') (hg : ng ≤ ng') (ho : no ≤ no') :
    physicalContinuationBitBudget M P nr ng no B ≤ physicalContinuationBitBudget M P nr' ng' no' B := by
  unfold physicalContinuationBitBudget wideActionsBitBudget localContinuationBitBudget bellmanBitBudget
  dsimp only
  gcongr

theorem preparedLocalKernelWithWork_bounds {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
    (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval target.length → BinaryFraction)
    (old current : Fin M × TargetInterval target.length → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (query : TargetInterval target.length)
    (hb : PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S t
      tau a eta kappa delta parentInitial childMass childInitial old current history integer) :
    (preparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query).1.width ≤
        preparedKernelWordBudget M B ∧
      (preparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query).2 ≤
        preparedKernelBitBudget N M P F exponent eM eF B S := by
  let reps := localRepresentativesWithWork N P F a parentInitial query
  let groups := preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP
    tau a parentInitial childMass childInitial (fun i r => current (i, r)) draw query
  let online := preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
    parentInitial childMass childInitial history t integer query
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  have hMpos : 0 < M := by rw [hM]; exact Nat.two_pow_pos _
  have hr := localRepresentativesWithWork_cost N P F B a parentInitial query (by have := hb.largeBits; omega)
    hb.inputSize hb.factorSize hFpos hb.precisionSize hP (by have := hb.targetSize; omega)
    hb.factorWidth hb.parentSize
  have hg := preparedLocalCellGroupsWithWork_cost source target parent N P F exponent Q eM eF B hM hF hP
    tau a parentInitial childMass childInitial (fun i r => current (i, r)) draw query
    (by have := hb.largeBits; omega) hb.inputSize hb.sourceSize hb.targetSize hb.aritySize hb.sampleSize
    hb.precisionSize hb.factorSize hb.thetaSize hb.scaleSizes hb.tauSize hb.factorWidth hb.parentSize
    hb.massSize hb.initialSize (fun i r => hb.currentSize (i, r)) (hb.parentNonneg query) hPdyadic
  have ho := preparedLocalOnlineActionsWithWork_cost source target parent N P F exponent H B E S hP hMpos
    tau a eta kappa parentInitial childMass childInitial history t integer query
    (by have := hb.largeBits; omega) hb.inputSize hb.sourceSize hb.targetSize (by have := hb.aritySize; omega)
    hb.precisionSize hb.factorSize hb.thetaSize hb.heightSize hb.coordinateSize hb.iterationSize hb.drawSize
    hb.tauSize hb.factorWidth hb.rateSize hb.optimismSize hb.parentSize hb.massSize hb.initialSize
    hb.historySize hb.rateMagnitude hb.optimismRange hb.historyRange hb.scalePositive hb.arityCap
    hb.precisionCap hb.rateCap hb.timeCap hb.wordCap hb.actionCap hb.cartesianCap hb.iterationCap
  have htail := physicalContinuationWithWork_bounds parent reps.1 P F (B + 4) delta (parentInitial query)
    old current groups.1 online.1 query hP (by have := hb.largeBits; omega)
    (by have := hb.sourceSize; omega) (by have := hb.targetSize; omega)
    (by have := hb.aritySize; omega) (by have := hb.precisionSize; omega) (by have := hb.factorSize; omega)
    (fun br hbr => (localRepresentativesWithWork_scale_bits N P F B hP a parentInitial query hb.inputSize br hbr).trans
      (by omega))
    (hb.decrementSize.trans (by omega)) ((hb.parentSize query).trans (by omega))
    (fun s => (hb.oldSize s).trans (by omega)) (fun s => (hb.currentSize s).trans (by omega))
    (fun action ha => preparedLocalCellGroupsWithWork_connection source target parent N P F exponent Q eM eF
      hM hF hP tau a parentInitial childMass childInitial (fun i r => current (i, r)) draw query
      (B + 4) (by have := hb.targetSize; omega) action ha)
    (by
      intro action ha
      rw [preparedLocalOnlineActionsWithWork_connection source target parent N P F exponent H hP
        tau a eta kappa parentInitial childMass childInitial history t integer query action ha]
      change 1 ≤ connectionWordBudget M (B + 4)
      unfold connectionWordBudget bandMassTotalStorageBudget
      omega)
  have hrlen := localRepresentativesWithWork_length_le N P F B hP hFpos a parentInitial query hb.inputSize
  have hglen := preparedLocalCellGroupsWithWork_length_le source target parent N P F exponent Q eM eF B
    hM hF hP tau a parentInitial childMass childInitial (fun i r => current (i, r)) draw query
    hb.inputSize (hb.parentNonneg query)
  have holen := preparedLocalOnlineActionsWithWork_length_le source target parent N P F exponent H B hP
    tau a eta kappa parentInitial childMass childInitial history t integer query hb.inputSize
  have htailCost := htail.2.trans (physicalContinuationBitBudget_mono_counts M P _ _ _ _ _ _ (B + 4)
    hrlen hglen holen)
  refine ⟨htail.1, ?_⟩
  change reps.2 + groups.2 + online.2 +
    (physicalContinuationWithWork parent reps.1 P F delta (parentInitial query) old current groups.1 online.1 query).2 + 4 ≤ _
  change reps.2 ≤ _ at hr
  change groups.2 ≤ _ at hg
  change online.2 ≤ _ at ho
  unfold preparedKernelBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
