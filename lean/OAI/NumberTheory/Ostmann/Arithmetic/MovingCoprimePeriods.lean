import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingDenominators

namespace OAI

/-! # Coprimality of the actual arithmetic and spectator periods -/

namespace Ostmann
open scoped Classical

private theorem aux_parts {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (p : ℕ)
    (h : p.Coprime (movingAuxiliaryUnitPeriod value outside
      (.node s CL CR U left right)).natAbs) :
    p.Coprime (s.natAbs * MovingSlotReversal.naturalProduct value U) ∧
    p.Coprime (movingAuxiliaryUnitPeriod value outside left).natAbs ∧
    p.Coprime (movingAuxiliaryUnitPeriod value outside right).natAbs := by
  simp only [movingAuxiliaryUnitPeriod, Int.natAbs_mul, Int.natAbs_natCast,
    Nat.coprime_mul_iff_right] at h
  exact ⟨h.1.1.2.1.mul_right h.1.1.2.2, h.1.2, h.2⟩

theorem MovingSlotData.formulaNodes_period_coprime {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (p : ℕ) (hfreq : T.Frequencies (fun s => p.Coprime s.natAbs))
    (haux : p.Coprime (movingAuxiliaryUnitPeriod value outside T).natAbs)
    (L R : HistoryFormula Bool)
    (hL : p.Coprime L.cleared.denominator.natAbs)
    (hR : p.Coprime R.cleared.denominator.natAbs) :
    p.Coprime (movingArithmeticPeriod (T.formulaNodes value hvalue childBound pivotBound hf L R)) := by
  induction T generalizing L R with
  | leaf => simp [formulaNodes, movingArithmeticPeriod]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right false
    let hu := MovingSlotReversal.naturalProduct_ne_zero value hvalue U
    let G := step.giantFormula value hf.1 hu L R
    obtain ⟨hcomp, hauxL, hauxR⟩ := aux_parts value outside s CL CR U left right p haux
    have hG : p.Coprime G.cleared.denominator.natAbs := by
      rw [step.giantFormula_denominator value hf.1 hu L R]
      simpa only [Int.natAbs_mul, Int.natAbs_natCast, step, MovingSlotData.step] using (hcomp.mul_right hL).mul_right hR
    have hl := ihL hf.2.1 hfreq.2.1 hauxL G L hG hL
    have hr := ihR hf.2.2 hfreq.2.2 hauxR G R hG hR
    have hhead : p.Coprime
        ({ guard := (movingNodeGuard (MovingSlotReversal.naturalProduct value step.leftSlots)
            (MovingSlotReversal.naturalProduct value step.rightSlots)
            step.rootFrequency step.leftFrequency step.rightFrequency hf.1
            (childBound (n + 1)) (pivotBound (n + 1)) L R),
           newGiant := G } : MovingFormulaNode).residuePeriod := by
      rw [movingNode_residuePeriod step value hf.1 hu]
      exact ((((hfreq.1.pow_right 3).mul_right hfreq.2.2.root).mul_right
        (Nat.coprime_mul_iff_right.mp hcomp).2).mul_right (hL.pow_right 2)).mul_right (hR.pow_right 3)
    simpa only [MovingSlotData.formulaNodes, movingArithmeticPeriod, List.map_cons,
      List.map_append, List.prod_cons, List.prod_append, G, step, MovingSlotData.step] using hhead.mul_right (hl.mul_right hr)

theorem movingTopPeriod_coprime_of_auxiliary {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (p : ℕ) (hfreq : T.Frequencies (fun s => p.Coprime s.natAbs))
    (haux : p.Coprime (movingAuxiliaryUnitPeriod value outside T).natAbs) :
    p.Coprime (movingTopPeriod value hvalue childBound pivotBound T hf) := by
  exact T.formulaNodes_period_coprime value hvalue outside childBound pivotBound hf p hfreq haux
    (.prime false) (.prime true) (by simp [HistoryFormula.cleared, ClearedHistoryValue.ofVariable])
    (by simp [HistoryFormula.cleared, ClearedHistoryValue.ofVariable])

theorem movingSpectatorDenominator_dvd_auxiliary {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) {n : ℕ} (T : MovingSlotData σ n) :
    movingSpectatorDenominator value T ∣ movingAuxiliaryUnitPeriod value outside T := by
  induction T with
  | leaf => exact one_dvd _
  | node s CL CR U left right ihL ihR =>
    change s * (MovingSlotReversal.naturalProduct value U : ℤ) * _ * _ ∣ _
    have h := mul_dvd_mul (mul_dvd_mul (dvd_refl
      (s * (MovingSlotReversal.naturalProduct value U : ℤ))) ihL) ihR
    exact h.trans ⟨(MovingSlotData.node s CL CR U left right).frequencyProduct * outside.prod, by
      dsimp only [movingAuxiliaryUnitPeriod]
      ring⟩

end Ostmann

end OAI
