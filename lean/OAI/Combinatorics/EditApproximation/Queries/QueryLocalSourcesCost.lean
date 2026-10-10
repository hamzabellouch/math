import OAI.Combinatorics.EditApproximation.Queries.QueryLocalSources
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalRefinementCost
import OAI.Combinatorics.EditApproximation.Queries.QuerySourceGatherCost
import OAI.Combinatorics.EditApproximation.Queries.QueryBufferedSourceBounds

namespace OAI

/-! The complete random-source stage: source enumeration and range construction,
physical source reads, finite-buffer scans, and the inner local refinement. -/

namespace EditApproximation.BinaryFraction

def queryLocalSourcesBitBudget (M N P F exponent eM eF B S t Rp R W : ℕ) : ℕ :=
  queryGroupGatherBitBudget M F exponent eM eF B Rp W
    (queryOnlineGatherBitBudget M P B Rp R W
      (queryLocalRefinementBitBudget M N P F exponent eM eF B S t Rp R W
        (queryBufferedGroupReadBudget M F exponent eM eF B B)
        (queryOnlineBufferReadBudget (B + 1) B B)))

end EditApproximation.BinaryFraction

namespace EditApproximation
section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalRandomSources_work_bound (Rp W : ℕ)
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp)
    (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work oracle readWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work oracle readWork ≤ W)
    (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W)
    (hb :
      let groupKeys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (parentInitial q).1 q).1
      let groupWords := groupKeys.map fun key => (readGroup key).value oracle
      let onlineKeys := (queryOnlineKeysWithWork N P F hP a (parentInitial q).1 q).1
      let onlineWords := onlineKeys.map fun key =>
        (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle
      let draw := queryGroupDrawReadWithWork groupKeys groupWords
      let integer := queryOnlineIntegerReadWithWork onlineKeys onlineWords
      let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
      let earlierWords := earlier.map fun key => (readEarlier key).value oracle
      let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
        (parentInitial q).1 q draw).1
      let sharedWords := shared.map fun key => (readCurrent key).value oracle
      PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
        tau a eta kappa delta (fun r => (parentInitial r).1)
        (fun i r => (child i r).1) (fun i r => (initial i r).1)
        (fun input => (queryHistoryReadWithWork earlier earlierWords (t - 1) input).1)
        (fun input => (queryChildReadWithWork shared sharedWords input.1 input.2).1)
        (fun s input => (queryHistoryReadWithWork earlier earlierWords s input).1)
        (fun b r => (integer b r).1)) :
    (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial child initial R hc hi q
      readGroup readInteger readEarlier readCurrent).work oracle readWork ≤
      queryLocalSourcesBitBudget M N P F exponent eM eF B S t Rp R W := by
  let groupKeys := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (parentInitial q).1 q).1
  let groupWords := groupKeys.map fun key => (readGroup key).value oracle
  let onlineKeys := (queryOnlineKeysWithWork N P F hP a (parentInitial q).1 q).1
  let onlineWords := onlineKeys.map fun key =>
    (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle
  let draw := queryGroupDrawReadWithWork groupKeys groupWords
  let integer := queryOnlineIntegerReadWithWork onlineKeys onlineWords
  have hB : 10 ≤ B := hb.largeBits
  have hnx : Nat.size source.length ≤ B := by have := hb.sourceSize; omega
  have hny : Nat.size target.length ≤ B := by have := hb.targetSize; omega
  have hMb : Nat.size M ≤ B := by have := hb.aritySize; omega
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  have hgw : ∀ w ∈ groupWords, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hgW key
  have how : ∀ w ∈ onlineWords, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hzW key _
  have hdg := queryBufferedGroupReadCost exponent eM eF B B hM hF a (parentInitial q).1 q groupWords
    (by omega) hb.inputSize hb.factorSize hb.aritySize hb.sampleSize
    (by have := hb.scaleSizes; omega) hb.thetaSize hny hb.factorWidth (hb.parentSize q)
    (hb.parentNonneg q) (by omega) hgw
  have hdo := queryBufferedOnlineReadCost N P F B B hP a (parentInitial q).1 q onlineWords
    (by omega) hb.inputSize hb.factorSize hFpos hb.precisionSize hny hb.factorWidth
    (hb.parentSize q) (by omega) how
  have hlocal := queryLocalRefinement_work_bound source target parent N P F exponent H Q eM eF B E S
    hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer q
    readEarlier readCurrent oracle readWork Rp W _ _ htime ht hPd hp heW hcW
    (fun key hk => heR key ((Nat.size_le_size
      (queryEarlierInputsWithWork_time M parent N P F exponent t hP a parentInitial q key hk).le).trans ht))
    hcR hdg (fun e he _ => hdo e he) hb
  have hgCost : ∀ key ∈ groupKeys, (readGroup key).work oracle readWork ≤ W := by
    intro key hk
    apply hgR key
    exact queryGroupSourceKeysWithWork_width M N F Q exponent eM eF B hM hF a (parentInitial q).1 q
      (by omega) hb.inputSize hb.factorSize hMb (by have := hb.scaleSizes; omega)
      hb.thetaSize hny hb.factorWidth (hb.parentSize q) (hb.parentNonneg q) key hk
  have hzCost : ∀ key ∈ onlineKeys,
      (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).work oracle readWork ≤ W := by
    intro key hk
    have hscale := queryOnlineKeysWithWork_scale N P F B hP a (parentInitial q).1 q
      hb.inputSize hFpos key hk
    apply hzR key _ hscale
    have hr := (queryOnlineRangeWithWork_bounds source target parent P exponent H (B + 1) R hP tau child key
      (by omega) (by omega) (by omega) (by omega) hscale (by have := hb.precisionSize; omega)
      (by have := hb.thetaSize; omega) (by have := hb.heightSize; omega)
      (by have := hb.coordinateSize; omega) (hb.tauSize.trans (by omega))
      (fun i r => (hb.massSize i r).trans (by omega)) hc).1
    simpa only [Nat.add_assoc] using hr
  unfold queryLocalRandomSources queryLocalSourcesBitBudget
  apply queryGroupSourceGather_work_bound M N F Q exponent eM eF B Rp W _ hM hF a parentInitial q
    readGroup _ oracle readWork (by omega) hb.inputSize hb.factorSize hb.aritySize hb.sampleSize
    (by have := hb.scaleSizes; omega) hb.thetaSize hny hb.factorWidth (hb.parentSize q)
    (hb.parentNonneg q) (hp q) hgCost
  apply queryOnlineSourceGather_work_bound source target parent N P F exponent H B Rp R W _ hP tau a
    parentInitial child q readInteger _ oracle readWork (by omega) hb.inputSize hb.factorSize hFpos
    hMb hb.precisionSize hb.thetaSize hnx hny hb.heightSize hb.coordinateSize hb.tauSize hb.factorWidth
    (hb.parentSize q) (hp q) hb.massSize hc hzCost
  exact hlocal

end Sources
end EditApproximation

end OAI
