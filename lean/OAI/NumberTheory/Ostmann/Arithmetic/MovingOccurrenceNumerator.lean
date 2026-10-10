import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceIntegrality
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceUnits

namespace OAI

/-! # Identifying the occurrence lines with the actual integer numerators -/

namespace Ostmann
open scoped Classical

theorem movingSlotLine_integer_numerator {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (XL XR : ℕ)
    (hvalid : MovingSlotPathIntegral value path (XL, XR))
    (hunit : ∀ s ∈ path,
      MovingSlotReversal.naturalReduction q value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.u ≠ 0) :
    let φ := MovingSlotReversal.naturalReduction q value
    let pair := movingSlotNaturalPath value path (XL, XR)
    ((movingSlotLine path current).normalized φ).1 * (XL : ZMod q) +
      ((movingSlotLine path current).normalized φ).2 * (XR : ZMod q) =
        (current.leftFrequency : ZMod q) *
            ((pair.2 * MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : ZMod q) -
          (current.rightFrequency : ZMod q) *
            ((pair.1 * MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : ZMod q) := by
  let φ := MovingSlotReversal.naturalReduction q value
  let T := movingPolynomialAncestors (path.map MovingSlotReversal.polynomial)
  have hden : φ T.denominator ≠ 0 := by
    apply movingPolynomialAncestors_denominator
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact (hunit t ht).2.2
  have he := movingSlotNaturalPath_realized value path (XL, XR) hvalid hunit
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change (T.normalized φ).a * (XL : ZMod q) + (T.normalized φ).b * XR = _ at hL
  change (T.normalized φ).c * (XL : ZMod q) + (T.normalized φ).d * XR = _ at hR
  change ((T.numeratorLine current.polynomial.v current.polynomial.w).normalized φ).1 *
      (XL : ZMod q) +
    ((T.numeratorLine current.polynomial.v current.polynomial.w).normalized φ).2 * XR = _
  rw [PolynomialGiantRows.normalized_numeratorLine T _ _ φ hden]
  dsimp only
  calc
    _ = φ current.polynomial.v * ((T.normalized φ).c * XL + (T.normalized φ).d * XR) -
        φ current.polynomial.w * ((T.normalized φ).a * XL + (T.normalized φ).b * XR) := by ring
    _ = _ := by
      rw [hL, hR]
      simp only [φ, MovingSlotReversal.naturalReduction, MovingSlotReversal.polynomial,
        MovingSlotReversal.coefficient_nat_eval, Nat.cast_mul]
      ring

/-- All prerequisites of the numerator identity now follow from the original
numeric tree support and the actual type-separated sampled primes. -/
theorem sampled_occurrence_numerator {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (XL XR : ℕ)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, n ≤ tier i)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, n ≤ tier i)
    (hsamples : samples.Levels tier)
    (hI : (buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value)).Integral
      XL XR (movingSlotValues value n bulk))
    (o : MovingSlotOccurrence σ) (ho : o ∈ (buildMovingSlotData n t small bulk samples).occurrences)
    (rep : σ) (hrep : tier rep < o.level)
    (hfreq : movingGiantFrequencyUnits (value rep) n t) :
    let _ : Fact (value rep).Prime := ⟨hprime rep⟩
    let φ := MovingSlotReversal.naturalReduction (value rep) value
    let pair := movingSlotNaturalPath value o.path (XL, XR)
    ((movingSlotLine o.path o.current).normalized φ).1 * (XL : ZMod (value rep)) +
      ((movingSlotLine o.path o.current).normalized φ).2 * (XR : ZMod (value rep)) =
        (o.current.leftFrequency : ZMod (value rep)) *
            ((pair.2 * MovingSlotReversal.naturalProduct value o.current.rightSlots : ℕ) : ZMod (value rep)) -
          (o.current.rightFrequency : ZMod (value rep)) *
            ((pair.1 * MovingSlotReversal.naturalProduct value o.current.leftSlots : ℕ) : ZMod (value rep)) := by
  let : Fact (value rep).Prime := ⟨hprime rep⟩
  have hlevels := buildMovingSlotData_levels tier n t small bulk samples hsmall hbulk hsamples
  have hfreq' := buildMovingSlotData_frequencyUnits n t small bulk samples hfreq
  have hu := MovingSlotData.occurrence_units_of_prime_types tier value hprime hdisjoint
    _ hlevels o ho rep hrep hfreq'
  have hi := buildMovingSlotData_occurrence_integral value n t small bulk samples XL XR hI o ho
  exact movingSlotLine_integer_numerator value o.path o.current XL XR hi.1 hu.1

end Ostmann

end OAI
