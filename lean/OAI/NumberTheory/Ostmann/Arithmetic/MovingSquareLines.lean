import OAI.NumberTheory.Ostmann.Arithmetic.MovingClearedRows
import OAI.NumberTheory.Ostmann.Arithmetic.SquareLiftExclusions

namespace OAI

/-! # Prime-square exclusions for the actual moving occurrence lines -/

namespace Ostmann
open scoped BigOperators Classical

@[simp] theorem naturalReduction_square {σ : Type*} (p : ℕ) (value : σ → ℕ)
    (f : MvPolynomial σ ℤ) :
    squareReduction p (MovingSlotReversal.naturalReduction (p ^ 2) value f) =
      MovingSlotReversal.naturalReduction p value f := by
  have he : (squareReduction p).comp (MovingSlotReversal.naturalReduction (p ^ 2) value) =
      MovingSlotReversal.naturalReduction p value := by
    ext i <;> simp [MovingSlotReversal.naturalReduction]
  exact DFunLike.congr_fun he f

theorem movingSlotLine_square_denominator_unit {σ : Type*} {p : ℕ} [Fact p.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ)) (current : MovingSlotReversal σ)
    (hu : ∀ s ∈ path, MovingSlotReversal.naturalReduction p value s.polynomial.u ≠ 0) :
    IsUnit (MovingSlotReversal.naturalReduction (p ^ 2) value
      (movingSlotLine path current).denominator) := by
  apply (isUnit_square_iff _).mpr
  rw [naturalReduction_square]
  apply movingPolynomialAncestors_denominator
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact hu t ht

/-- The exact numerator test modulo p² is the cleared line test at the two
original giants. Only ancestor denominators need to be units. -/
theorem movingSlotLine_square_zero_iff {σ : Type*} {p : ℕ} [Fact p.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (XL XR : ℕ)
    (hvalid : MovingSlotPathIntegral value path (XL, XR))
    (hu : ∀ s ∈ path, MovingSlotReversal.naturalReduction p value s.polynomial.u ≠ 0) :
    let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
    let pair := movingSlotNaturalPath value path (XL, XR)
    φ (movingSlotLine path current).a * (XL : ZMod (p ^ 2)) +
        φ (movingSlotLine path current).b * (XR : ZMod (p ^ 2)) = 0 ↔
      (p : ℤ) ^ 2 ∣
        current.leftFrequency *
            ((pair.2 * MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : ℤ) -
          current.rightFrequency *
            ((pair.1 * MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : ℤ) := by
  let N : ℤ := current.leftFrequency *
    (((movingSlotNaturalPath value path (XL, XR)).2 *
      MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : ℤ) -
    current.rightFrequency *
    (((movingSlotNaturalPath value path (XL, XR)).1 *
      MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : ℤ)
  have he : MovingSlotReversal.naturalReduction (p ^ 2) value (movingSlotLine path current).a *
        (XL : ZMod (p ^ 2)) +
      MovingSlotReversal.naturalReduction (p ^ 2) value (movingSlotLine path current).b * (XR : ZMod (p ^ 2)) =
      MovingSlotReversal.naturalReduction (p ^ 2) value
        (movingSlotLine path current).denominator * (N : ZMod (p ^ 2)) := by
    simpa only [MovingSlotReversal.naturalReduction, N, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast] using
      movingSlotLine_cleared_numerator (R := ZMod (p ^ 2)) value path current XL XR hvalid
  change _ = 0 ↔ (p : ℤ) ^ 2 ∣ N
  rw [he, (movingSlotLine_square_denominator_unit value path current hu).mul_right_eq_zero]
  convert ZMod.intCast_zmod_eq_zero_iff_dvd N (p ^ 2) using 1
  norm_cast

/-- The uniform lift loss for any finite collection of actual occurrences.
All rows are proved nonzero from the ancestor and current frequency units. -/
theorem movingSlotLines_square_loss {σ I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (value : σ → ℕ) (path : I → List (MovingSlotReversal σ))
    (current : I → MovingSlotReversal σ)
    (hunit : ∀ i s, s ∈ path i →
      MovingSlotReversal.naturalReduction p value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction p value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction p value s.polynomial.u ≠ 0)
    (hc : ∀ i, MovingSlotReversal.naturalReduction p value (current i).polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction p value (current i).polynomial.w ≠ 0)
    (x₀ y₀ : ZMod p) (hy : y₀ ≠ 0)
    (hbase : ∀ i, MovingSlotReversal.naturalReduction p value (movingSlotLine (path i) (current i)).a * x₀ +
      MovingSlotReversal.naturalReduction p value (movingSlotLine (path i) (current i)).b * y₀ = 0)
    (F : SquareLiftPairs p x₀ y₀ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ v, ‖F v‖ ≤ B) :
    let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
    ‖∑ v ∈ Finset.univ.filter (fun v : SquareLiftPairs p x₀ y₀ => ∃ i,
      φ (movingSlotLine (path i) (current i)).a * v.1.1 +
        φ (movingSlotLine (path i) (current i)).b * v.2.1 = 0), F v‖ / (p : ℝ) ^ 2 ≤
      B * (Fintype.card I : ℝ) / p := by
  apply square_lift_nonzero_rows_removed_mass_le _ _ x₀ y₀ hy
  · intro i
    simp only [naturalReduction_square]
    apply movingHistoryLine_nonzero
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      exact hunit i t ht
    · exact (hc i).1
    · exact (hc i).2
  · simpa only [naturalReduction_square] using hbase
  · exact hB
  · exact hF

end Ostmann

end OAI
