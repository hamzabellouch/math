import OAI.Combinatorics.EditApproximation.Queries.QueryLocalRefinement
import OAI.Combinatorics.EditApproximation.Queries.QuerySelectorCost
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalFinishCost
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryBufferCost
import OAI.Combinatorics.EditApproximation.Queries.QuerySharedInputCost
import OAI.Combinatorics.EditApproximation.Queries.QueryRefinementWorkBound

namespace OAI

namespace EditApproximation.BinaryFraction

def queryRefinementReadBudget (B Rp R earlier shared : ℕ) : ℕ :=
  R + Rp + (1 + earlier * (32 * B + 12)) + (1 + shared * (24 * B + 9))

def queryLocalRefinementBitBudget (M N P F exponent eM eF B S t Rp R W Dg Do : ℕ) : ℕ :=
  let earlier := queryHistoryInputsLength M P t (queryEarlierRepresentativesLength P F exponent B)
  let shared := querySharedInputsLength M F exponent eM eF B
  let groups := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let U := queryRefinementReadBudget B Rp R earlier shared
  queryRefinementStagesBudget M B W earlier (queryEarlierInputsBitBudget M P F exponent t B Rp)
    (B + 1) (preparedLocalOnlineBitBudget M P B S * tableReadFactor U * (Do + 4))
    shared (querySharedInputsBitBudget M F exponent eM eF B Dg)
    groups (preparedLocalGroupsBitBudget N M P F exponent eM eF B * tableReadFactor U * (Dg + 4)) Rp
    (queryRefinementFinishBitBudget M P F B (queryFinishReadBudget M B Rp earlier groups (B + 1)) groups (B + 1))

end EditApproximation.BinaryFraction

namespace EditApproximation
section Local
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalRefinement_work_bound (Rp W Dg Do : ℕ)
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (heR : ∀ key ∈ (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1,
      (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W)
    (hdg : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ Dg)
    (hdo : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial q).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤ Do)
    (hb :
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
    (queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
      parentInitial child initial R hc hi draw integer q readEarlier readCurrent).work oracle readWork ≤
      queryLocalRefinementBitBudget M N P F exponent eM eF B S t Rp R W Dg Do := by
  let earlier := queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q
  let earlierWords := earlier.1.map fun key => (readEarlier key).value oracle
  let shared := querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a (parentInitial q).1 q draw
  let sharedWords := shared.1.map fun key => (readCurrent key).value oracle
  let EL := queryHistoryInputsLength M P t (queryEarlierRepresentativesLength P F exponent B)
  let SL := querySharedInputsLength M F exponent eM eF B
  let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let U := queryRefinementReadBudget B Rp R EL SL
  change PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
    tau a eta kappa delta (fun r => (parentInitial r).1) (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun input => (queryHistoryReadWithWork earlier.1 earlierWords (t - 1) input).1)
    (fun input => (queryChildReadWithWork shared.1 sharedWords input.1 input.2).1)
    (fun s input => (queryHistoryReadWithWork earlier.1 earlierWords s input).1) (fun b r => (integer b r).1) at hb
  have hB : 10 ≤ B := hb.largeBits
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  have hnx : Nat.size source.length ≤ B := by have := hb.sourceSize; omega
  have hny : Nat.size target.length ≤ B := by have := hb.targetSize; omega
  have hMb : Nat.size M ≤ B := by have := hb.aritySize; omega
  have hE := queryEarlierInputsWithWork_bounds M N P F exponent t B Rp parent hP a parentInitial q
    (by omega) hb.inputSize hb.factorSize hFpos hb.precisionSize hnx hny hMb ht hb.thetaSize
    hb.factorWidth hb.parentSize hp (hb.parentNonneg q) hPd
  have hSh := querySharedInputsWithWork_bounds_on M N F Q exponent eM eF B Dg hM hF parent a
    (parentInitial q).1 q draw (by omega) hb.inputSize hb.factorSize hb.aritySize hb.sampleSize hb.scaleSizes
    hb.thetaSize hnx hny hb.factorWidth (hb.parentSize q) (hb.parentNonneg q) (by
      intro eb heb cell hcell
      have hmem := heb
      simp only [queryExponentsWithWork, filterWithWork_value, List.mem_filter] at hmem
      exact hdg eb hmem.1 hmem.2 cell hcell)
  have hEU : ∀ s ≤ t - 1 + 1, ∀ input,
      (queryHistoryReadWithWork earlier.1 earlierWords s input).2 ≤ U := by
    intro s hs input
    have hs' : s ≤ t := by omega
    have hr := queryHistoryReadWithWork_cost earlier.1 earlierWords s input B hMb hny
      ((Nat.size_le_size hs').trans ht) (fun key hk =>
        (Nat.size_le_size (queryEarlierInputsWithWork_time M parent N P F exponent t hP a parentInitial q key hk).le).trans ht)
    have hm := Nat.mul_le_mul_right (32 * B + 12) hE.1
    change earlier.1.length * (32 * B + 12) ≤ EL * (32 * B + 12) at hm
    dsimp only [U, queryRefinementReadBudget]
    omega
  have hSU : ∀ i r, (queryChildReadWithWork shared.1 sharedWords i r).2 ≤ U := by
    intro i r
    have hr := queryChildReadWithWork_cost shared.1 sharedWords i r B hMb hny
    have hm := Nat.mul_le_mul_right (24 * B + 9) hSh.1
    change shared.1.length * (24 * B + 9) ≤ SL * (24 * B + 9) at hm
    dsimp only [U, queryRefinementReadBudget]
    omega
  have hRU : R ≤ U := by dsimp only [U, queryRefinementReadBudget]; omega
  have hpU : ∀ r, (parentInitial r).2 ≤ U := by
    intro r
    exact (hp r).trans (by dsimp only [U, queryRefinementReadBudget]; omega)
  have hcU : ∀ i r, (child i r).2 ≤ U := fun i r => (hc i r).trans hRU
  have hiU : ∀ i r, (initial i r).2 ≤ U := fun i r => (hi i r).trans hRU
  have hg := queryGroupSelectWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM hF tau a eta kappa delta t parentInitial child initial R U hc hi hcU hiU hpU draw integer
    earlier.1 earlierWords shared.1 sharedWords q hb hPd hSU Dg hdg
  have ho := queryOnlineSelectWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM tau a eta kappa delta t parentInitial child initial R U hc hi hcU hiU hpU integer
    earlier.1 earlierWords shared.1 sharedWords q hb hEU Do hdo
  have heWords : ∀ w ∈ earlierWords, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact heW key
  have heTimes : ∀ key ∈ earlier.1, Nat.size key.2.1 ≤ B := by
    intro key hk
    exact (Nat.size_le_size (queryEarlierInputsWithWork_time M parent N P F exponent t hP a parentInitial q key hk).le).trans ht
  unfold queryLocalRefinement
  apply queryRefinementGather_work_bound source target parent N P F exponent Q eM eF hP hM hF a t
    parentInitial draw q readEarlier readCurrent _ _ _ oracle readWork B W EL _ (B + 1) _ SL _ G _ _ Rp hMb hny
  · exact hE.1
  · exact hE.2
  · exact ho.1
  · exact ho.2
  · exact hSh.1
  · exact hSh.2
  · exact hg.1
  · exact hg.2
  · exact heR
  · exact hcR
  · let current := queryNeededInputsWithWork
      (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
        parentInitial child initial R hc hi draw shared.1 sharedWords q).1
      (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
        parentInitial child initial R hc hi t integer earlier.1 earlierWords q).1
    have hw : ∀ w ∈ current.1.map (fun key => (readCurrent key).value oracle), w.width ≤ B := by
      intro w hw
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
      exact hcW key
    have hf := queryLocalRefinement_finish_bounds source target parent N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer
      earlier.1 earlierWords shared.1 sharedWords (current.1.map fun key => (readCurrent key).value oracle) q
      B Rp EL hB hb.inputSize hnx hb.targetSize hMb hb.precisionSize hb.factorSize ht hb.factorWidth
      hb.decrementSize hb.parentSize hp (hb.parentNonneg q) heWords hw heTimes hE.1
    simpa only [BitQuery.compute, BitQuery.work, Nat.add_zero] using hf.2
  · exact hp q

end Local
end EditApproximation

end OAI
