import OAI.Combinatorics.EditApproximation.Queries.QueryLocalBand
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalSourcesCost
import OAI.Combinatorics.EditApproximation.Queries.QueryOuterGatherCost
import OAI.Combinatorics.EditApproximation.Queries.QueryBufferedInputBounds
import OAI.Combinatorics.EditApproximation.Queries.QueryNumericInteger

namespace OAI

namespace EditApproximation.BinaryFraction

def queryBandReadBudget (M P F exponent B : ℕ) : ℕ :=
  1 + queryEarlierRepresentativesLength P F exponent B * (M * (40 * P + 2) ^ 2) * (24 * B + 9)

theorem queryLocalSourcesBitBudget_mono_reads (M N P F exponent eM eF B S t Rp W R R' : ℕ)
    (hR : R ≤ R') :
    queryLocalSourcesBitBudget M N P F exponent eM eF B S t Rp R W ≤
      queryLocalSourcesBitBudget M N P F exponent eM eF B S t Rp R' W := by
  unfold queryLocalSourcesBitBudget queryGroupGatherBitBudget queryOnlineGatherBitBudget
    queryOnlineRangeBitBudget queryLocalRefinementBitBudget queryRefinementStagesBudget
    queryRefinementReadBudget tableReadFactor
  dsimp only
  gcongr

def queryLocalBandBitBudget (M N P F exponent eM eF B S t Rp W : ℕ) : ℕ :=
  queryBandGatherBitBudget M P F exponent B Rp W
    (queryLocalSourcesBitBudget M N P F exponent eM eF B S t Rp
      (queryBandReadBudget M P F exponent B) W)

end EditApproximation.BinaryFraction

namespace EditApproximation
section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalBand_work_bound (Rp W : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E S (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp)
    (hpW : ∀ r, (parentInitial r).1.width ≤ B)
    (hpN : ∀ r, 0 ≤ (parentInitial r).1.value)
    (hmW : ∀ key, ((readMass key).value oracle).width ≤ B)
    (hiW : ∀ key, ((readInitial key).value oracle).width ≤ B)
    (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (hiN : ∀ key, 0 ≤ ((readInitial key).value oracle).value)
    (heN : ∀ key, 0 ≤ ((readEarlier key).value oracle).value)
    (heI : ∀ key, ((readEarlier key).value oracle).value ≤
      ((readInitial (key.1, key.2.2)).value oracle).value)
    (hmR : ∀ key, (readMass key).work oracle readWork ≤ W)
    (hiR : ∀ key, (readInitial key).work oracle readWork ≤ W)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work oracle readWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work oracle readWork ≤ W)
    (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W) :
    (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger
      q readEarlier readCurrent).work oracle readWork ≤
      queryLocalBandBitBudget M N P F exponent eM eF B S t Rp W := by
  have hB : 10 ≤ B := hn.largeBits
  have hnx : Nat.size source.length ≤ B := by have := hn.sourceSize; omega
  have hny : Nat.size target.length ≤ B := by have := hn.targetSize; omega
  have hMb : Nat.size M ≤ B := by have := hn.aritySize; omega
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  let keys := (queryBandInputsWithWork M parent N P F exponent hP a parentInitial q).1
  let massWords := keys.map fun key => (readMass key).value oracle
  let initialWords := keys.map fun key => (readInitial key).value oracle
  let R := queryDataReadBudget M target.length keys
  have hk := (queryBandInputsWithWork_bounds M N P F exponent B Rp parent hP a parentInitial q
    (by omega) hn.inputSize hn.factorSize hFpos hn.precisionSize hnx hny hMb hn.thetaSize
    hn.factorWidth hpW hp (hpN q) hPd).1
  have hR : R ≤ queryBandReadBudget M P F exponent B := by
    dsimp only [R, queryDataReadBudget, queryBandReadBudget]
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul hk (by omega)
  unfold queryLocalBand queryLocalBandBitBudget
  apply queryBandGather_work_bound M N P F exponent B Rp W _ parent hP a parentInitial q
    readMass readInitial _ oracle readWork (by omega) hn.inputSize hn.factorSize hFpos
    hn.precisionSize hnx hny hMb hn.thetaSize hn.factorWidth hpW hp (hpN q) hPd hmR hiR
  apply le_trans _ (queryLocalSourcesBitBudget_mono_reads M N P F exponent eM eF B S t Rp W R _ hR)
  apply queryLocalRandomSources_work_bound source target parent N P F exponent H Q eM eF B E S hP hM hF
    tau a eta kappa delta t parentInitial (queryChildReadWithWork keys massWords)
    (queryChildReadWithWork keys initialWords) R
    (queryChildReadWithWork_budget keys massWords) (queryChildReadWithWork_budget keys initialWords)
    q readGroup readInteger readEarlier readCurrent oracle readWork Rp W htime ht hPd hp
    hgW hzW heW hcW hgR hzR heR hcR
  dsimp only
  apply queryBufferedRefinementInputBounds parent N P F exponent H Q eM eF B E S t Rp hP
    tau a eta kappa delta parentInitial hp q massWords _ _
    (fun key => (readEarlier key).value oracle) (fun key => (readInitial key).value oracle) _
  · apply hn.with_integer
    intro b r
    apply queryOnlineIntegerReadWithWork_size _ _ b r B (by omega)
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hzW key _
  · exact hpW
  · exact hpN
  · intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hmW key
  · intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hcW key
  · exact hiW
  · exact heW
  · exact hiN
  · exact heN
  · exact heI

end Band
end EditApproximation

end OAI
