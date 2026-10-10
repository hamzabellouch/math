import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairSquareLoss
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalBaseAverage
import OAI.NumberTheory.Ostmann.Construction.ExternalSquareFibers

namespace OAI

/-! # Relative local square loss above the actual simultaneous line system -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingInternalPairFactor_fiber {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x₀ y₀ : ZMod p) (v : SquareLiftPairs p x₀ y₀) :
    movingInternalPairFactor value T p v.1.1 v.2.1 =
      movingInternalBaseFactor value T p x₀ y₀ *
        (if ∀ j : MovingPrimeOccurrences value T p,
          let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
          let L := movingPrimeOccurrenceLine value T p j
          φ L.a * v.1.1 + φ L.b * v.2.1 ≠ 0 then 1 else 0) := by
  let A := ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction p value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * x₀ + φ L.b * y₀ = 0
  let B := ∀ j : MovingPrimeOccurrences value T p,
    let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
    let L := movingPrimeOccurrenceLine value T p j
    φ L.a * v.1.1 + φ L.b * v.2.1 ≠ 0
  have hs : (∀ side, movingInternalLocalSupport value (T side) p v.1.1 v.2.1) ↔ A ∧ B := by
    rw [movingInternalLocalSupport_occurrences]
    simp only [map_add, map_mul, naturalReduction_square, v.1.property, v.2.property]
    exact forall_and
  change (if ∀ side, movingInternalLocalSupport value (T side) p v.1.1 v.2.1 then 1 else 0) =
    (if A then 1 else 0) * (if B then 1 else 0)
  by_cases ha : A
  · by_cases hb : B
    · simp only [ite_eq_left (hs.mpr ⟨ha, hb⟩), ite_eq_left ha, ite_eq_left hb, mul_one]
    · simp only [ite_eq_right (fun h => hb (hs.mp h).2), ite_eq_left ha, ite_eq_right hb, mul_zero]
  · simp only [ite_eq_right (fun h => ha (hs.mp h).1), ite_eq_right ha, zero_mul]

/-- The square loss is relative to the base line event. The number of
forbidden zero lifts is bounded by the number of nodes in the two histories. -/
theorem movingInternalPairFactor_fiber_error {σ : Type*} {n : ℕ}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (T : Bool → MovingSlotData σ n) (hlevels : ∀ side, (T side).Levels tier)
    (p : ℕ) [Fact p.Prime]
    (hf : ∀ side, (T side).Frequencies (fun s => (s : ZMod p) ≠ 0))
    (x₀ y₀ : ZMod p) (hy : y₀ ≠ 0)
    (hbase : ∀ j : MovingPrimeOccurrences value T p,
      let φ := MovingSlotReversal.naturalReduction p value
      let L := movingPrimeOccurrenceLine value T p j
      φ L.a * x₀ + φ L.b * y₀ = 0) :
    ((p : ℝ) ^ 2)⁻¹ *
      ‖(∑ v : SquareLiftPairs p x₀ y₀, movingInternalPairFactor value T p v.1.1 v.2.1) -
        (p : ℂ) ^ 2‖ ≤ 2 * (2 ^ n - 1 : ℕ) / (p : ℝ) := by
  let J := MovingPrimeOccurrences value T p
  let φ := MovingSlotReversal.naturalReduction (p ^ 2) value
  let L := movingPrimeOccurrenceLine value T p
  let bad := fun v : SquareLiftPairs p x₀ y₀ => ∃ j : J, φ (L j).a * v.1.1 + φ (L j).b * v.2.1 = 0
  have hr (j : J) : squareReduction p (φ (L j).a) ≠ 0 ∨ squareReduction p (φ (L j).b) ≠ 0 := by
    simp only [φ, naturalReduction_square]
    exact movingPrimeOccurrenceLine_nonzero tier value hprime hdisjoint T hlevels p hf j
  have hlocal := square_lift_nonzero_rows_removed_mass_le
    (fun j : J => φ (L j).a) (fun j : J => φ (L j).b) x₀ y₀ hy hr
    (by simpa only [φ, naturalReduction_square] using hbase)
    (fun _ => (1 : ℂ)) 1 (by norm_num) (by simp)
  have hid (v : SquareLiftPairs p x₀ y₀) :
      movingInternalPairFactor value T p v.1.1 v.2.1 - 1 = -(if bad v then 1 else 0) := by
    rw [movingInternalPairFactor_on_fiber value T p x₀ y₀ hbase]
    change (if ∀ j : J, φ (L j).a * v.1.1 + φ (L j).b * v.2.1 ≠ 0 then 1 else 0) - 1 =
      -(if bad v then 1 else 0)
    by_cases h : bad v
    · have hn : ¬ ∀ j : J, φ (L j).a * v.1.1 + φ (L j).b * v.2.1 ≠ 0 := by
        obtain ⟨j, hj⟩ := h
        exact fun hall => hall j hj
      simp only [ite_eq_right hn, ite_eq_left h, zero_sub]
    · have hg : ∀ j : J, φ (L j).a * v.1.1 + φ (L j).b * v.2.1 ≠ 0 := not_exists.mp h
      simp only [ite_eq_left hg, ite_eq_right h, sub_self, neg_zero]
  have hsum : (∑ v : SquareLiftPairs p x₀ y₀, movingInternalPairFactor value T p v.1.1 v.2.1) -
      (p : ℂ) ^ 2 = -(∑ v ∈ Finset.univ.filter bad, (1 : ℂ)) := by
    calc
      _ = ∑ v : SquareLiftPairs p x₀ y₀, (movingInternalPairFactor value T p v.1.1 v.2.1 - 1) := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, squareLiftPairs_card, Nat.cast_pow]
      _ = ∑ v : SquareLiftPairs p x₀ y₀, -(if bad v then 1 else 0) := Finset.sum_congr rfl (fun v _ => hid v)
      _ = _ := by rw [Finset.sum_neg_distrib, Finset.sum_filter]
  rw [hsum, norm_neg]
  have hbound : (Fintype.card J : ℝ) / p ≤ 2 * (2 ^ n - 1 : ℕ) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast movingPrimeOccurrences_card value T p
  have he : ((p : ℝ) ^ 2)⁻¹ * ‖∑ v ∈ Finset.univ.filter bad, (1 : ℂ)‖ ≤
      (Fintype.card J : ℝ) / p := by
    simpa only [bad, φ, L, J, one_mul, div_eq_mul_inv, mul_comm] using hlocal
  exact he.trans hbound

end Ostmann

end OAI
