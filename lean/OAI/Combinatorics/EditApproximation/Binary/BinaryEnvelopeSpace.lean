import OAI.Combinatorics.EditApproximation.Binary.BinaryReductionSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryOptimizerSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryEnvelopeReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Scratch replay for the bounded dyadic scan and the actual band
initial-value reads used to form each child envelope. -/

namespace EditApproximation.BinaryFraction



theorem dyadicScanAllocation_le_work (a candidate : BinaryFraction) (n : ℕ) :
    dyadicScanAllocation a candidate n ≤ (dyadicScanWithWork a candidate n).2 := by
  induction n generalizing candidate with
  | zero => simp only [dyadicScanAllocation, dyadicScanWithWork]; exact Nat.zero_le _
  | succ n ih =>
    have hc := ltAllocation_le_work candidate a
    have ht := ih (doubleFraction candidate)
    unfold dyadicScanAllocation dyadicScanWithWork
    dsimp only
    split_ifs <;> dsimp only
    · exact (Nat.add_assoc _ _ _).symm.le.trans
        (Nat.add_le_add (Nat.add_le_add hc ht) (by decide : 1 ≤ 2))
    · exact Nat.add_le_add hc (Nat.zero_le 1)



theorem dyadicCeilingAllocation_le_work (a : BinaryFraction) :
    dyadicCeilingAllocation a ≤ (dyadicCeilingWithWork a).2 := by
  have h := dyadicScanAllocation_le_work a (inversePowerTwo a.width) (2 * a.width)
  unfold dyadicCeilingAllocation dyadicCeilingWithWork
  dsimp only
  omega



theorem bandEnvelopeReadAllocation_le_work {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) (i : Fin M)
    (h : ∀ action ∈ band, footprint i (action i) ≤ (read i (action i)).2) :
    bandEnvelopeReadAllocation b band read footprint i ≤ (bandEnvelopeReadWithWork b band read i).2 := by
  have hv := arithmeticMapAllocation_le_work (fun action => read i (action i))
    (fun action => footprint i (action i)) band h
  let values := (arithmeticMapWithWork (fun action => read i (action i)) band).1
  have hd := divAllocation_le_work (nat b) (nat M)
  have hm := maximumAllocation_le_work zero values
  have hx := maxAllocation_le_work (divWithWork (nat b) (nat M)).1 (maximumWithWork zero values).1
  have he := dyadicCeilingAllocation_le_work
    (maxWithWork (divWithWork (nat b) (nat M)).1 (maximumWithWork zero values).1).1
  unfold bandEnvelopeReadAllocation bandEnvelopeReadWithWork
  dsimp only
  dsimp only [values] at hm hx he
  omega



theorem envelopeVectorReadAllocation_le_work {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ)
    (h : ∀ i action, action ∈ band → footprint i (action i) ≤ (read i (action i)).2) :
    envelopeVectorReadAllocation b band read footprint ≤ (envelopeVectorReadWithWork b band read).2 := by
  exact vectorMapAllocation_le_work M _ _ (fun i => bandEnvelopeReadAllocation_le_work b band read footprint i (h i))

def dyadicScanInvocations (a candidate : BinaryFraction) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    compareInvocations candidate a + if (candidate.ltWithWork a).1 then
      dyadicScanInvocations a (doubleFraction candidate) n + 1 else 1

theorem dyadicScanInvocations_le_work (a candidate : BinaryFraction) (n : ℕ) :
    dyadicScanInvocations a candidate n ≤ (dyadicScanWithWork a candidate n).2 := by
  induction n generalizing candidate with
  | zero => simp only [dyadicScanInvocations, dyadicScanWithWork]; omega
  | succ n ih =>
    have hc := compareInvocations_le_work candidate a
    have ht := ih (doubleFraction candidate)
    unfold dyadicScanInvocations dyadicScanWithWork
    dsimp only
    split_ifs <;> dsimp only <;> omega

def dyadicCeilingInvocations (a : BinaryFraction) : ℕ :=
  dyadicScanInvocations a (inversePowerTwo a.width) (2 * a.width) + a.width + 2

theorem dyadicCeilingInvocations_le_work (a : BinaryFraction) :
    dyadicCeilingInvocations a ≤ (dyadicCeilingWithWork a).2 := by
  have h := dyadicScanInvocations_le_work a (inversePowerTwo a.width) (2 * a.width)
  unfold dyadicCeilingInvocations dyadicCeilingWithWork
  dsimp only
  omega

def bandEnvelopeReadInvocations {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) (i : Fin M) : ℕ :=
  let values := (arithmeticMapWithWork (fun action => read i (action i)) band).1
  let floor := (divWithWork (nat b) (nat M)).1
  let maximum := (maximumWithWork zero values).1
  arithmeticMapInvocations (fun action => footprint i (action i)) band +
    divInvocations (nat b) (nat M) + maximumInvocations zero values + maxInvocations floor maximum +
    dyadicCeilingInvocations (maxWithWork floor maximum).1 + 1

theorem bandEnvelopeReadInvocations_le_work {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) (i : Fin M)
    (h : ∀ action ∈ band, footprint i (action i) ≤ (read i (action i)).2) :
    bandEnvelopeReadInvocations b band read footprint i ≤ (bandEnvelopeReadWithWork b band read i).2 := by
  have hv := arithmeticMapInvocations_le_work (fun action => read i (action i))
    (fun action => footprint i (action i)) band h
  let values := (arithmeticMapWithWork (fun action => read i (action i)) band).1
  have hd := divInvocations_le_work (nat b) (nat M)
  have hm := maximumInvocations_le_work zero values
  have hx := maxInvocations_le_work (divWithWork (nat b) (nat M)).1 (maximumWithWork zero values).1
  have he := dyadicCeilingInvocations_le_work
    (maxWithWork (divWithWork (nat b) (nat M)).1 (maximumWithWork zero values).1).1
  unfold bandEnvelopeReadInvocations bandEnvelopeReadWithWork
  dsimp only
  dsimp only [values] at hm hx he
  omega

def envelopeVectorReadInvocations {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ) : ℕ :=
  vectorMapInvocations M (bandEnvelopeReadInvocations b band read footprint)

theorem envelopeVectorReadInvocations_le_work_add_one {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (footprint : Fin M → TargetInterval n → ℕ)
    (h : ∀ i action, action ∈ band → footprint i (action i) ≤ (read i (action i)).2) :
    envelopeVectorReadInvocations b band read footprint ≤ (envelopeVectorReadWithWork b band read).2 + 1 := by
  exact vectorMapInvocations_le_work_add_one M _ _ (fun i => bandEnvelopeReadInvocations_le_work b band read footprint i (h i))

end EditApproximation.BinaryFraction

end OAI
