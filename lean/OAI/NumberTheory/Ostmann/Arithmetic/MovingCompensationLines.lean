import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceSquares
import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticSupport

namespace OAI

/-! # Compensation divisibility is the current internal-prime line condition

The equivalence below is used before imposing integrality of the new giant.
Thus the line condition recovers the original compensation division instead
of merely being a consequence of an already integral history.
-/

namespace Ostmann
open scoped Classical

theorem pairwise_coprime_list_prod_dvd_iff (U : List ℕ)
    (hU : U.Pairwise Nat.Coprime) (Q : ℕ) :
    U.prod ∣ Q ↔ ∀ b ∈ U, b ∣ Q := by
  constructor
  · intro h b hb
    exact (List.dvd_prod hb).trans h
  · induction U with
    | nil => simp
    | cons b U ih =>
      intro h
      obtain ⟨hbU, hUU⟩ := List.pairwise_cons.mp hU
      have hb := h b (by simp)
      have ht := ih hUU (fun c hc => h c (List.mem_cons_of_mem b hc))
      exact (Nat.coprime_list_prod_right_iff.mpr hbU).mul_dvd_of_dvd_of_dvd hb ht

theorem compensation_dvd_iff_numerator (U : List ℕ) (s N : ℤ) (Q : ℕ)
    (hprime : ∀ b ∈ U, b.Prime) (hpair : U.Pairwise Nat.Coprime)
    (hs : ∀ b ∈ U, ¬ b ∣ s.natAbs) (hN : N = s * Q) :
    U.prod ∣ Q ↔ ∀ b ∈ U, (b : ℤ) ∣ N := by
  rw [pairwise_coprime_list_prod_dvd_iff U hpair Q]
  apply forall₂_congr
  intro b hb
  rw [hN]
  have hcop : IsCoprime (b : ℤ) s := by
    simpa only [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast] using
      ((hprime b hb).coprime_iff_not_dvd.mpr (hs b hb))
  constructor
  · intro h
    exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr h) s
  · intro h
    exact Int.natCast_dvd_natCast.mp (hcop.dvd_of_dvd_mul_left h)

/-- The cleared line and the actual current numerator have the same zero
test modulo an internal prime. Only the earlier path must be integral. -/
theorem movingSlotLine_prime_zero_iff {σ : Type*} {p : ℕ} [Fact p.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (XL XR : ℕ)
    (hvalid : MovingSlotPathIntegral value path (XL, XR))
    (hu : ∀ s ∈ path, MovingSlotReversal.naturalReduction p value s.polynomial.u ≠ 0) :
    let φ := MovingSlotReversal.naturalReduction p value
    φ (movingSlotLine path current).a * (XL : ZMod p) +
        φ (movingSlotLine path current).b * (XR : ZMod p) = 0 ↔
      (p : ℤ) ∣ current.integerNumerator value (movingSlotNaturalPath value path (XL, XR)) := by
  have hd : MovingSlotReversal.naturalReduction p value
      (movingSlotLine path current).denominator ≠ 0 := by
    apply movingPolynomialAncestors_denominator
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hu t ht
  have he := movingSlotLine_cleared_numerator (R := ZMod p) value path current XL XR hvalid
  change _ = 0 ↔ _
  have hn : MovingSlotReversal.naturalReduction p value (movingSlotLine path current).a *
        (XL : ZMod p) +
      MovingSlotReversal.naturalReduction p value (movingSlotLine path current).b * (XR : ZMod p) =
      MovingSlotReversal.naturalReduction p value (movingSlotLine path current).denominator *
        (current.integerNumerator value (movingSlotNaturalPath value path (XL, XR)) : ZMod p) := by
    simpa only [MovingSlotReversal.naturalReduction, MovingSlotReversal.integerNumerator,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast] using he
  rw [hn, mul_eq_zero, or_iff_right hd]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ p

/-- At a supported transfer node, the internal-prime congruences are
equivalent to the original compensation-product divisibility. -/
theorem moving_compensation_division_iff_lines {σ : Type*}
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (XL XR Q : ℕ)
    (hvalid : MovingSlotPathIntegral value path (XL, XR))
    (hprime : ∀ i ∈ current.compensationSlots, (value i).Prime)
    (hpair : (current.compensationSlots.map value).Pairwise Nat.Coprime)
    (hs : ∀ i ∈ current.compensationSlots, ¬ value i ∣ current.rootFrequency.natAbs)
    (hu : ∀ i ∈ current.compensationSlots, ∀ s ∈ path,
      MovingSlotReversal.naturalReduction (value i) value s.polynomial.u ≠ 0)
    (hN : current.integerNumerator value (movingSlotNaturalPath value path (XL, XR)) =
      current.rootFrequency * Q) :
    MovingSlotReversal.naturalProduct value current.compensationSlots ∣ Q ↔
      ∀ i ∈ current.compensationSlots,
        let φ := MovingSlotReversal.naturalReduction (value i) value
        φ (movingSlotLine path current).a * (XL : ZMod (value i)) +
          φ (movingSlotLine path current).b * (XR : ZMod (value i)) = 0 := by
  rw [MovingSlotReversal.naturalProduct,
    compensation_dvd_iff_numerator _ _ _ _
      (by intro b hb; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact hprime i hi)
      hpair (by intro b hb; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; exact hs i hi) hN]
  constructor
  · intro h i hi
    let : Fact (value i).Prime := ⟨hprime i hi⟩
    exact (movingSlotLine_prime_zero_iff value path current XL XR hvalid (hu i hi)).mpr
      (h (value i) (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    let : Fact (value i).Prime := ⟨hprime i hi⟩
    exact (movingSlotLine_prime_zero_iff value path current XL XR hvalid (hu i hi)).mp (h i hi)

/-- Every internal-prime line of the original integral tree vanishes. This
uses the actual occurrence path and allows a prime to represent several nodes. -/
theorem MovingSlotData.integral_compensation_lines {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hfreq : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) :
    ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
      let φ := MovingSlotReversal.naturalReduction (value i) value
      φ (movingSlotLine o.path o.current).a * (XL : ZMod (value i)) +
        φ (movingSlotLine o.path o.current).b * (XR : ZMod (value i)) = 0 := by
  intro o ho i hi
  let : Fact (value i).Prime := ⟨hprime i⟩
  have hu := T.occurrence_units_of_prime_types tier value hprime hdisjoint hlevels
    o ho i (T.occurrence_compensation_level tier hlevels o ho i hi) (hfreq i)
  have hv := T.occurrence_integral value XL XR hI o ho
  apply (movingSlotLine_prime_zero_iff value o.path o.current XL XR hv.1
    (fun s hs => (hu.1 s hs).2.2)).mpr
  have hd : value i ∣ MovingSlotReversal.naturalProduct value o.current.compensationSlots :=
    List.dvd_prod (List.mem_map.mpr ⟨i, hi, rfl⟩)
  change (value i : ℤ) ∣ _
  rw [show o.current.integerNumerator value (movingSlotNaturalPath value o.path (XL, XR)) =
      o.current.rootFrequency * ((MovingSlotReversal.naturalProduct value o.current.compensationSlots *
        o.current.naturalPivot value (movingSlotNaturalPath value o.path (XL, XR)).1
          (movingSlotNaturalPath value o.path (XL, XR)).2 : ℕ) : ℤ) from hv.2.2]
  exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_left hd _)) _

end Ostmann

end OAI
