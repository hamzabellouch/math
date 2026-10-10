import OAI.NumberTheory.Ostmann.Arithmetic.MovingFormulaNodes

namespace OAI

/-! # Exact arithmetic support of the constructed moving formulas -/

namespace Ostmann
open scoped Classical

theorem MovingSlotReversal.giantFormula_of_composite {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (XL XR Q : ℕ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ))
    (hQ : step.leftFrequency * ((XR * MovingSlotReversal.naturalProduct value step.rightSlots : ℕ) : ℤ) -
      step.rightFrequency * ((XL * MovingSlotReversal.naturalProduct value step.leftSlots : ℕ) : ℤ) =
        step.rootFrequency * (Q : ℤ)) :
    (step.giantFormula value hs hu L R).value (fun b => (a b : ℚ)) =
      (Q : ℚ) / MovingSlotReversal.naturalProduct value step.compensationSlots := by
  have he := congrArg (fun z : ℤ => (z : ℚ)) hQ
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
  simp only [giantFormula, HistoryFormula.value_solve, HistoryFormula.value_product,
    HistoryFormula.value_external, hL, hR, Int.cast_mul, Int.cast_natCast]
  rw [he]
  field_simp

/-- This support is exactly the original node validity together with the
sampled compensation division. It also specifies the actual child giants. -/
def MovingSlotData.ArithmeticSupport {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | n + 1, .node s CL CR u left right, XL, XR =>
      ∃ Q : ℕ, ValidTransferNode (movingSlotSystem value childBound pivotBound)
          ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency Q ∧
        MovingSlotReversal.naturalProduct value u ∣ Q ∧
        left.ArithmeticSupport value childBound pivotBound (Q / MovingSlotReversal.naturalProduct value u) XL ∧
        right.ArithmeticSupport value childBound pivotBound (Q / MovingSlotReversal.naturalProduct value u) XR

/-- The finite list of rational formulas characterizes every original
arithmetic condition. In particular the reverse implication retains the
compensation divisibility; no new support assumption is introduced. -/
theorem MovingSlotData.formulaNodes_iff {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (L R : HistoryFormula Bool) (a : Bool → ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ)) :
    (∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R,
      f.guard.ValidAt a ∧ f.newGiant.IntegralAt a) ↔
      T.ArithmeticSupport value childBound pivotBound XL XR := by
  induction T generalizing XL XR L R with
  | leaf s regular => simp [formulaNodes, ArithmeticSupport]
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    let U := MovingSlotReversal.naturalProduct value u
    have hU : U ≠ 0 := MovingSlotReversal.naturalProduct_ne_zero value hvalue u
    let G := step.giantFormula value hf.1 hU L R
    let g := movingNodeGuard (MovingSlotReversal.naturalProduct value CL)
      (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hf.1
      (childBound (n + 1)) (pivotBound (n + 1)) L R
    have hg := movingNodeGuard_iff value childBound pivotBound s CL CR u left right hf.1 XL XR L R a hL hR
    have hformula (Q : ℕ)
        (hQ : ValidTransferNode (movingSlotSystem value childBound pivotBound)
          ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency Q) :
        G.value (fun b => (a b : ℚ)) = (Q : ℚ) / U := by
      apply step.giantFormula_of_composite value hf.1 hU L R a XL XR Q hL hR
      exact hQ.relation
    have hGint (Q : ℕ)
        (hQ : ValidTransferNode (movingSlotSystem value childBound pivotBound)
          ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency Q) :
        G.IntegralAt a ↔ U ∣ Q := by
      simp only [HistoryFormula.IntegralAt, hformula Q hQ]
      exact rational_nat_div_integral_iff Q U hU
    have hGvalue (Q : ℕ)
        (hQ : ValidTransferNode (movingSlotSystem value childBound pivotBound)
          ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency Q)
        (hdiv : U ∣ Q) : G.value (fun b => (a b : ℚ)) = (Q / U : ℕ) := by
      rw [hformula Q hQ]
      calc
        (Q : ℚ) / U = ((U * (Q / U) : ℕ) : ℚ) / U :=
          congrArg (fun z : ℕ => (z : ℚ) / U) (Nat.mul_div_cancel' hdiv).symm
        _ = _ := by
          rw [Nat.cast_mul]
          exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hU)
    change (∀ f ∈ ({ guard := g, newGiant := G } ::
      (left.formulaNodes value hvalue childBound pivotBound hf.2.1 G L ++
        right.formulaNodes value hvalue childBound pivotBound hf.2.2 G R) : List MovingFormulaNode),
      f.guard.ValidAt a ∧ f.newGiant.IntegralAt a) ↔ _
    constructor
    · intro hall
      have hroot := hall ⟨g, G⟩ (by simp)
      obtain ⟨Q, hQ⟩ := hg.mp hroot.1
      have hd := (hGint Q hQ).mp hroot.2
      have hv := hGvalue Q hQ hd
      refine ⟨Q, hQ, hd, ?_, ?_⟩
      · apply (ihL hf.2.1 (Q / U) XL G L hv hL).mp
        intro f hmem
        exact hall f (List.mem_cons_of_mem _ (List.mem_append_left _ hmem))
      · apply (ihR hf.2.2 (Q / U) XR G R hv hR).mp
        intro f hmem
        exact hall f (List.mem_cons_of_mem _ (List.mem_append_right _ hmem))
    · rintro ⟨Q, hQ, hd, hl, hr⟩
      have hv := hGvalue Q hQ hd
      have hleft := (ihL hf.2.1 (Q / U) XL G L hv hL).mpr hl
      have hright := (ihR hf.2.2 (Q / U) XR G R hv hR).mpr hr
      intro f hmem
      rcases List.mem_cons.mp hmem with h | h
      · subst f
        exact ⟨hg.mpr ⟨Q, hQ⟩, (hGint Q hQ).mpr hd⟩
      · rcases List.mem_append.mp h with h | h
        · exact hleft f h
        · exact hright f h

end Ostmann

end OAI
