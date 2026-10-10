import OAI.Combinatorics.EditApproximation.Queries.QueryLocalProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalBandCost

namespace OAI

/-! A complete work bound for the actual adaptive local program. Premises
are numeric parameter bounds, stored-word sizes, and the existing history
range invariant; all intermediate enumeration and scans are included. -/

namespace EditApproximation.BinaryFraction

def queryParentBufferReadBudget (P F exponent B : ℕ) : ℕ :=
  1 + queryInitialSupportLength P F exponent B * (16 * B + 6)

def queryLocalProgramBitBudget (M N P F exponent eM eF B S t W : ℕ) : ℕ :=
  queryInitialGatherBitBudget P F exponent B W
    (queryLocalBandBitBudget M N P F exponent eM eF B S t
      (queryParentBufferReadBudget P F exponent B) W)

end EditApproximation.BinaryFraction

namespace EditApproximation
section Program
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (readParent : TargetInterval target.length → BitQuery ι BinaryFraction)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalProgram_work_bound (W : ℕ)
    (hn : PreparedKernelNumericBounds (nx := source.length) (ny := target.length) (M := M)
      N P F exponent H Q eM eF B E S (t - 1) tau a eta kappa delta (fun _ _ => 0))
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hpW : ∀ key, ((readParent key).value oracle).width ≤ B)
    (hmW : ∀ key, ((readMass key).value oracle).width ≤ B)
    (hiW : ∀ key, ((readInitial key).value oracle).width ≤ B)
    (hgW : ∀ key, ((readGroup key).value oracle).width ≤ B)
    (hzW : ∀ key range, ((readInteger key range).value oracle).width ≤ B)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (hpN : ∀ key, 0 ≤ ((readParent key).value oracle).value)
    (hiN : ∀ key, 0 ≤ ((readInitial key).value oracle).value)
    (heN : ∀ key, 0 ≤ ((readEarlier key).value oracle).value)
    (heI : ∀ key, ((readEarlier key).value oracle).value ≤
      ((readInitial (key.1, key.2.2)).value oracle).value)
    (hpR : ∀ key, (readParent key).work oracle readWork ≤ W)
    (hmR : ∀ key, (readMass key).work oracle readWork ≤ W)
    (hiR : ∀ key, (readInitial key).work oracle readWork ≤ W)
    (hgR : ∀ key, queryGroupKeySize key ≤ 40 * B + 500 →
      (readGroup key).work oracle readWork ≤ W)
    (hzR : ∀ key range, Nat.size key.1 ≤ B + 1 → Nat.size range ≤ 240 * (B + 5) + 7 →
      (readInteger key range).work oracle readWork ≤ W)
    (heR : ∀ key, Nat.size key.2.1 ≤ B → (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W) :
    (queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t readParent readMass readInitial readGroup readInteger
      q readEarlier readCurrent).work oracle readWork ≤
      queryLocalProgramBitBudget M N P F exponent eM eF B S t W := by
  have hB : 10 ≤ B := hn.largeBits
  have hny : Nat.size target.length ≤ B := by have := hn.targetSize; omega
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  let keys := (queryInitialSupportWithWork N P F exponent hP a ((readParent q).value oracle) q).1
  let words := keys.map fun key => (readParent key).value oracle
  have hkeys := (queryInitialSupportWithWork_bounds N P F exponent B hP a ((readParent q).value oracle) q
    (by omega) hn.inputSize hn.factorSize hFpos hn.precisionSize hny hn.thetaSize
    hn.factorWidth (hpW q) (hpN q) hPd).1
  have hpw : ∀ w ∈ words, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hpW key
  have hpr : ∀ r, (queryParentReadWithWork keys words r).2 ≤ queryParentBufferReadBudget P F exponent B := by
    intro r
    apply (queryParentReadWithWork_cost keys words r).trans
    unfold queryParentBufferReadBudget
    exact Nat.add_le_add_left (Nat.mul_le_mul hkeys (by omega)) 1
  have hpn : ∀ r, 0 ≤ (queryParentReadWithWork keys words r).1.value := by
    intro r
    rw [queryParentReadWithWork_value]
    apply finiteAnswerTable_nonneg
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact hpN key
  unfold queryLocalProgram queryLocalProgramBitBudget
  apply queryInitialGather_work_bound N P F exponent B W _ hP a q readParent _ oracle readWork
    (by omega) hn.inputSize hn.factorSize hFpos hn.precisionSize hny hn.thetaSize
    hn.factorWidth (hpW q) (hpN q) hPd hpR
  apply queryLocalBand_work_bound source target parent N P F exponent H Q eM eF B E S hP hM hF
    tau a eta kappa delta t (queryParentReadWithWork keys words) readMass readInitial readGroup readInteger
    q readEarlier readCurrent oracle readWork _ W hn htime ht hPd hpr
    (fun r => gatheredWordLookupWithWork_width _ keys words r B (by omega) hpw) hpn
    hmW hiW hgW hzW heW hcW hiN heN heI hmR hiR hgR hzR heR hcR

end Program
end EditApproximation

end OAI
