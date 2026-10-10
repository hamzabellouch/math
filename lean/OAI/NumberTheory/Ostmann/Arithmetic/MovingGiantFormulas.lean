import OAI.NumberTheory.Ostmann.Arithmetic.MovingNodeGuards

namespace OAI

/-! # Rational formulas retain the actual compensation division -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.giantFormula {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) : HistoryFormula Bool :=
  .solve (.product L (.external (MovingSlotReversal.naturalProduct value step.leftSlots)))
    (.product R (.external (MovingSlotReversal.naturalProduct value step.rightSlots)))
    step.leftFrequency step.rightFrequency
    (step.rootFrequency * (MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ))
    (mul_ne_zero hs (Int.natCast_ne_zero.mpr hu))

/-- A supported integer reconstruction evaluates the rational giant formula
exactly. The sampled compensation product appears in its denominator. -/
theorem MovingSlotReversal.giantFormula_value {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (XL XR : ℕ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ))
    (hI : step.IntegralAt value (XL, XR)) :
    (step.giantFormula value hs hu L R).value (fun b => (a b : ℚ)) =
      (step.naturalPivot value XL XR : ℚ) := by
  have he := congrArg (fun z : ℤ => (z : ℚ)) hI.2
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
  simp only [giantFormula, HistoryFormula.value_solve, HistoryFormula.value_product,
    HistoryFormula.value_external, hL, hR, Int.cast_mul, Int.cast_natCast]
  apply (div_eq_iff (mul_ne_zero (Int.cast_ne_zero.mpr hs) (Nat.cast_ne_zero.mpr hu))).mpr
  nlinarith only [he]

theorem MovingSlotReversal.giantFormula_integral {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (XL XR : ℕ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ))
    (hI : step.IntegralAt value (XL, XR)) :
    (step.giantFormula value hs hu L R).IntegralAt a := by
  refine ⟨(step.naturalPivot value XL XR : ℤ), ?_⟩
  simpa only [Int.cast_natCast] using step.giantFormula_value value hs hu L R a XL XR hL hR hI

/-- The extra division by u is represented by an integer-polynomial residue
test. It is not discarded when the ordinary transfer guards are idealized. -/
theorem rational_nat_div_integral_iff (P u : ℕ) (hu : u ≠ 0) :
    (∃ z : ℤ, (P : ℚ) / u = (z : ℚ)) ↔ u ∣ P := by
  constructor
  · rintro ⟨z, hz⟩
    have he := (div_eq_iff (Nat.cast_ne_zero.mpr hu)).mp hz
    have hi : (P : ℤ) = z * (u : ℤ) := by exact_mod_cast he
    have hd : (u : ℤ) ∣ (P : ℤ) := ⟨z, by simpa only [mul_comm] using hi⟩
    exact Int.natCast_dvd_natCast.mp hd
  · rintro ⟨z, rfl⟩
    refine ⟨(z : ℤ), ?_⟩
    simp only [Nat.cast_mul, Int.cast_natCast]
    exact mul_div_cancel_left₀ (z : ℚ) (Nat.cast_ne_zero.mpr hu)

end Ostmann

end OAI
