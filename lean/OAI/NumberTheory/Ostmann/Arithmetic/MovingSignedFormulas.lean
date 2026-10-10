import OAI.NumberTheory.Ostmann.Arithmetic.MovingIntegralFrequencySplit
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealResidues

namespace OAI

/-! # Original rational node formulas and the signed integer recursion -/

namespace Ostmann
open scoped Classical

theorem rational_int_div_integral_iff (N D : ℤ) (hD : D ≠ 0) :
    (∃ z : ℤ, (N : ℚ) / D = z) ↔ D ∣ N := by
  constructor
  · rintro ⟨z, hz⟩
    have he := (div_eq_iff (Int.cast_ne_zero.mpr hD)).mp hz
    have hi : N = z * D := by exact_mod_cast he
    exact ⟨z, by simpa only [mul_comm] using hi⟩
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    rw [Int.cast_mul]
    exact mul_div_cancel_left₀ (z : ℚ) (Int.cast_ne_zero.mpr hD)

theorem MovingSlotReversal.giantFormula_signed_value {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    (step.giantFormula value hs hu L R).value (fun b => (a b : ℚ)) =
      (step.signedNumerator value x y : ℚ) /
        (step.rootFrequency * (naturalProduct value step.compensationSlots : ℤ)) := by
  simp only [giantFormula, HistoryFormula.value_solve, HistoryFormula.value_product,
    HistoryFormula.value_external, hL, hR, signedNumerator, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast]

theorem MovingSlotReversal.giantFormula_signed_integral_iff {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    (step.giantFormula value hs hu L R).IntegralAt a ↔ step.SignedIntegralAt value x y := by
  change (∃ z : ℤ, (step.giantFormula value hs hu L R).value _ = (z : ℚ)) ↔ _
  rw [step.giantFormula_signed_value value hs hu L R a x y hL hR]
  simp only [← Int.cast_mul]
  rw [rational_int_div_integral_iff _ _ (mul_ne_zero hs (Int.natCast_ne_zero.mpr hu))]
  change _ ∣ _ ↔ _ = _
  constructor
  · intro hd
    exact (Int.mul_ediv_cancel' hd).symm
  · intro h
    exact ⟨step.signedPivot value x y, h⟩

theorem MovingSlotReversal.giantFormula_of_signed_integral {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ) (hs : step.rootFrequency ≠ 0)
    (hu : naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ))
    (hI : step.SignedIntegralAt value x y) :
    (step.giantFormula value hs hu L R).value (fun b => (a b : ℚ)) =
      (step.signedPivot value x y : ℚ) := by
  rw [step.giantFormula_signed_value value hs hu L R a x y hL hR, hI]
  push_cast
  field_simp

/-- The integrality entries of the original formula list impose exactly
the signed divisions. They do not need any real or positivity hypothesis. -/
theorem MovingSlotData.formulaNodes_signed_integral_iff {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (L R : HistoryFormula Bool) (a : Bool → ℤ) (x y : ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (x : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (y : ℚ)) :
    (∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R, f.newGiant.IntegralAt a) ↔
      T.SignedIntegral value x y := by
  induction T generalizing L R x y with
  | leaf => simp [formulaNodes, SignedIntegral]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right false
    have hU := MovingSlotReversal.naturalProduct_ne_zero value hvalue U
    let G := step.giantFormula value hf.1 hU L R
    have hroot := step.giantFormula_signed_integral_iff value hf.1 hU L R a x y hL hR
    simp only [formulaNodes, List.forall_mem_cons, List.forall_mem_append]
    change (G.IntegralAt a ∧ (∀ f ∈ left.formulaNodes value hvalue childBound pivotBound hf.2.1 G L,
      f.newGiant.IntegralAt a) ∧ (∀ f ∈ right.formulaNodes value hvalue childBound pivotBound hf.2.2 G R,
      f.newGiant.IntegralAt a)) ↔ _
    constructor
    · rintro ⟨hG, hl, hr⟩
      have hI := hroot.mp hG
      have hval := step.giantFormula_of_signed_integral value hf.1 hU L R a x y hL hR hI
      exact ⟨hI, (ihL hf.2.1 G L _ _ hval hL).mp hl, (ihR hf.2.2 G R _ _ hval hR).mp hr⟩
    · rintro ⟨hI, hl, hr⟩
      have hval := step.giantFormula_of_signed_integral value hf.1 hU L R a x y hL hR hI
      exact ⟨hroot.mpr hI, (ihL hf.2.1 G L _ _ hval hL).mpr hl, (ihR hf.2.2 G R _ _ hval hR).mpr hr⟩

end Ostmann

end OAI
