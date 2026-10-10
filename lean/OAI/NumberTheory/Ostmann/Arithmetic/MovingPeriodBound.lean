import OAI.NumberTheory.Ostmann.Arithmetic.MovingDenominators

namespace OAI

/-! # Quantitative size of the constructed top-giant residue modulus -/

namespace Ostmann
open scoped Classical BigOperators

def MovingSlotData.CompensationBound {σ : Type*} (value : σ → ℕ) (B : ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ _ _ u left right =>
      MovingSlotReversal.naturalProduct value u ≤ B ∧
        left.CompensationBound value B ∧ right.CompensationBound value B

def movingPeriodExponent (n d : ℕ) : ℕ := 2 * (4 ^ n - 1) * (d + 2)

theorem movingPeriodExponent_step (n d : ℕ) :
    5 * d + 5 + 2 * movingPeriodExponent n (2 * d + 2) ≤ movingPeriodExponent (n + 1) d := by
  have ht : 4 ^ (n + 1) - 1 = 4 * (4 ^ n - 1) + 3 := by
    have hp : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ]
    omega
  unfold movingPeriodExponent
  rw [ht]
  nlinarith

theorem MovingSlotReversal.giantFormula_denominator_bound {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (B d : ℕ)
    (hS : step.rootFrequency.natAbs ≤ B)
    (hU : MovingSlotReversal.naturalProduct value step.compensationSlots ≤ B)
    (hL : L.cleared.denominator.natAbs ≤ B ^ d) (hR : R.cleared.denominator.natAbs ≤ B ^ d) :
    (step.giantFormula value hs hu L R).cleared.denominator.natAbs ≤ B ^ (2 * d + 2) := by
  rw [step.giantFormula_denominator value hs hu L R]
  simp only [Int.natAbs_mul, Int.natAbs_natCast]
  calc
    _ ≤ B * B * B ^ d * B ^ d := by gcongr
    _ = B ^ 2 * (B ^ d * B ^ d) := by ring
    _ = B ^ (2 + (d + d)) := by rw [← pow_add, ← pow_add]
    _ = _ := by congr 1; omega

theorem movingNode_residuePeriod_bound {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) (B d : ℕ)
    (hS : step.rootFrequency.natAbs ≤ B) (hW : step.rightFrequency.natAbs ≤ B)
    (hU : MovingSlotReversal.naturalProduct value step.compensationSlots ≤ B)
    (hL : L.cleared.denominator.natAbs ≤ B ^ d) (hR : R.cleared.denominator.natAbs ≤ B ^ d) :
    ({ guard := movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
          (MovingSlotReversal.naturalProduct value step.rightSlots)
          step.rootFrequency step.leftFrequency step.rightFrequency hs childBound pivotBound L R
       newGiant := step.giantFormula value hs hu L R } : MovingFormulaNode).residuePeriod ≤ B ^ (5 * d + 5) := by
  rw [movingNode_residuePeriod]
  calc
    _ ≤ B ^ 3 * B * B * (B ^ d) ^ 2 * (B ^ d) ^ 3 := by gcongr
    _ = _ := by simp only [← pow_mul, ← pow_add, ← pow_succ]; congr 1; omega

/-- All repeated ancestor denominators are counted in this estimate; no
squarefree simplification or independence of those factors is used. -/
theorem MovingSlotData.formulaNodes_period_bound {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (L R : HistoryFormula Bool)
    (B d : ℕ) (hB : 1 ≤ B) (hfreq : T.Frequencies (fun s => s.natAbs ≤ B))
    (hcomp : T.CompensationBound value B)
    (hL : L.cleared.denominator.natAbs ≤ B ^ d) (hR : R.cleared.denominator.natAbs ≤ B ^ d) :
    movingArithmeticPeriod (T.formulaNodes value hvalue childBound pivotBound hf L R) ≤
      B ^ movingPeriodExponent n d := by
  induction T generalizing L R d with
  | leaf s regular => simp [formulaNodes, movingArithmeticPeriod, movingPeriodExponent]
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    let hu := MovingSlotReversal.naturalProduct_ne_zero value hvalue u
    let G := step.giantFormula value hf.1 hu L R
    have hG := step.giantFormula_denominator_bound value hf.1 hu L R B d hfreq.1 hcomp.1 hL hR
    have hd : d ≤ 2 * d + 2 := by omega
    have hL' := hL.trans (Nat.pow_le_pow_right hB hd)
    have hR' := hR.trans (Nat.pow_le_pow_right hB hd)
    have hl := ihL hf.2.1 G L (2 * d + 2) hfreq.2.1 hcomp.2.1 hG hL'
    have hr := ihR hf.2.2 G R (2 * d + 2) hfreq.2.2 hcomp.2.2 hG hR'
    have hhead := movingNode_residuePeriod_bound step value hf.1 hu
      (childBound (n + 1)) (pivotBound (n + 1)) L R B d hfreq.1 hfreq.2.2.root hcomp.1 hL hR
    simp only [MovingSlotData.formulaNodes, movingArithmeticPeriod, List.map_cons,
      List.map_append, List.prod_cons, List.prod_append]
    calc
      _ ≤ B ^ (5 * d + 5) *
          (B ^ movingPeriodExponent n (2 * d + 2) * B ^ movingPeriodExponent n (2 * d + 2)) :=
        Nat.mul_le_mul hhead (Nat.mul_le_mul hl hr)
      _ = B ^ (5 * d + 5 + 2 * movingPeriodExponent n (2 * d + 2)) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_right hB (movingPeriodExponent_step n d)

theorem movingTopPeriod_bound {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (B : ℕ) (hB : 1 ≤ B)
    (hfreq : T.Frequencies (fun s => s.natAbs ≤ B)) (hcomp : T.CompensationBound value B) :
    movingTopPeriod value hvalue childBound pivotBound T hf ≤ B ^ (4 * (4 ^ n - 1)) := by
  have h := T.formulaNodes_period_bound value hvalue childBound pivotBound hf (.prime false) (.prime true)
    B 0 hB hfreq hcomp (by simp [HistoryFormula.cleared, ClearedHistoryValue.ofVariable])
    (by simp [HistoryFormula.cleared, ClearedHistoryValue.ofVariable])
  have he : movingPeriodExponent n 0 = 4 * (4 ^ n - 1) := by
    unfold movingPeriodExponent
    ring
  simpa only [movingTopPeriod, he] using h

end Ostmann

end OAI
