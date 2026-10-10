import OAI.Combinatorics.EditApproximation.Probability.FiniteBufferRanges
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryBufferCost
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalFinishCost

namespace OAI

/-! Intermediate output widths for the executed adaptive refinement. These
bounds concern the words produced before memo-table normalization. -/

namespace EditApproximation
open BinaryFraction

section Refinement
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction)

theorem queryLocalRefinement_width (B Rp : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcw : ∀ key, ((readCurrent key).value oracle).width ≤ B) :
    ((queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial child initial R hc hi draw integer q
      readEarlier readCurrent).value oracle).width ≤ preparedKernelWordBudget M B := by
  let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
  let ew := earlier.map fun key => (readEarlier key).value oracle
  let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
    (parentInitial q).1 q draw).1
  let sw := shared.map fun key => (readCurrent key).value oracle
  let groups := (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R hc hi draw shared sw q).1
  let online := (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
    parentInitial child initial R hc hi t integer earlier ew q).1
  let keys := (queryNeededInputsWithWork groups online).1
  let cw := keys.map fun key => (readCurrent key).value oracle
  have he : ∀ w ∈ ew, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hew key
  have hcur : ∀ w ∈ cw, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hcw key
  have het : ∀ key ∈ earlier, Nat.size key.2.1 ≤ B := by
    intro key hk
    exact (Nat.size_le_size (queryEarlierInputsWithWork_time M parent N P F exponent t hP a
      parentInitial q key hk).le).trans ht
  have h := (queryLocalRefinement_finish_bounds source target parent N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer earlier ew
    shared sw cw q B Rp earlier.length hB hN hnx hny hMb hPb hFb ht ha hd hpw hpr hpn he hcur het
    (Nat.le_refl _)).1
  simpa only [queryLocalRefinement, queryRefinementGather, BitQuery.value_bind,
    BitQuery.value_collect, BitQuery.compute, BitQuery.value] using h

end Refinement

section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
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
  (oracle : ι → BinaryFraction)

theorem queryLocalRandomSources_width (B Rp : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcw : ∀ key, ((readCurrent key).value oracle).width ≤ B) :
    ((queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial child initial R hc hi q readGroup readInteger
      readEarlier readCurrent).value oracle).width ≤ preparedKernelWordBudget M B := by
  let gk := (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a (parentInitial q).1 q).1
  let gw := gk.map fun key => (readGroup key).value oracle
  let ok := (queryOnlineKeysWithWork N P F hP a (parentInitial q).1 q).1
  let ow := ok.map fun key =>
    (readInteger key (queryOnlineRangeWithWork parent P exponent H tau child key).1).value oracle
  have h := queryLocalRefinement_width source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial child initial R hc hi (queryGroupDrawReadWithWork gk gw)
    (queryOnlineIntegerReadWithWork ok ow) q readEarlier readCurrent oracle B Rp hB hN hnx hny hMb
    hPb hFb ht ha hd hpw hpr hpn hew hcw
  simpa only [queryLocalRandomSources, queryGroupSourceGather, queryOnlineSourceGather,
    BitQuery.value_bind, BitQuery.value_collect, BitQuery.compute, BitQuery.value] using h

end Sources

section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction)

theorem queryLocalBand_width (B Rp : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ r, (parentInitial r).1.width ≤ B) (hpr : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpn : 0 ≤ (parentInitial q).1.value)
    (hew : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcw : ∀ key, ((readCurrent key).value oracle).width ≤ B) :
    ((queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger q
      readEarlier readCurrent).value oracle).width ≤ preparedKernelWordBudget M B := by
  let keys := (queryBandInputsWithWork M parent N P F exponent hP a parentInitial q).1
  let mw := keys.map fun key => (readMass key).value oracle
  let iw := keys.map fun key => (readInitial key).value oracle
  have h := queryLocalRandomSources_width source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial (queryChildReadWithWork keys mw)
    (queryChildReadWithWork keys iw) (queryDataReadBudget M target.length keys)
    (queryChildReadWithWork_budget keys mw) (queryChildReadWithWork_budget keys iw)
    q readGroup readInteger readEarlier readCurrent oracle B Rp hB hN hnx hny hMb hPb hFb ht ha hd
    hpw hpr hpn hew hcw
  simpa only [queryLocalBand, queryBandGather, BitQuery.value_bind,
    BitQuery.value_collect, BitQuery.compute, BitQuery.value] using h

end Band

section Program
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (readParent : TargetInterval target.length → BitQuery ι BinaryFraction)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction)

theorem queryLocalProgram_width (B : ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hnx : Nat.size source.length ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hMb : Nat.size M ≤ B) (hPb : Nat.size P ≤ B)
    (hFb : Nat.size F + 2 ≤ B) (ht : Nat.size t ≤ B) (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hpw : ∀ key, ((readParent key).value oracle).width ≤ B)
    (hpn : ∀ key, 0 ≤ ((readParent key).value oracle).value)
    (hew : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcw : ∀ key, ((readCurrent key).value oracle).width ≤ B) :
    ((queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q
      readEarlier readCurrent).value oracle).width ≤ preparedKernelWordBudget M B := by
  let keys := (queryInitialSupportWithWork N P F exponent hP a ((readParent q).value oracle) q).1
  let words := keys.map fun key => (readParent key).value oracle
  have hw : ∀ w ∈ words, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hpw key
  have hn : ∀ r, 0 ≤ (queryParentReadWithWork keys words r).1.value := by
    intro r
    rw [queryParentReadWithWork_value]
    apply finiteAnswerTable_nonneg
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hpn key
  have h := queryLocalBand_width source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t (queryParentReadWithWork keys words) readMass readInitial
    readGroup readInteger q readEarlier readCurrent oracle B
    (1 + keys.length * (16 * Nat.size target.length + 6)) hB hN hnx hny hMb hPb hFb ht ha hd
    (fun r => gatheredWordLookupWithWork_width _ keys words r B (by omega) hw)
    (queryParentReadWithWork_cost keys words) (hn q) hew hcw
  simpa only [queryLocalProgram, queryInitialGather, BitQuery.value_bind,
    BitQuery.value_collect, BitQuery.compute, BitQuery.value] using h

end Program
end EditApproximation

end OAI
