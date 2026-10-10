import OAI.NumberTheory.Ostmann.Arithmetic.MovingSquareSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSquareLines

namespace OAI

/-! # The full square support as the actual occurrence line tests -/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.integerNumerator {σ : Type*} (value : σ → ℕ)
    (s : MovingSlotReversal σ) (pair : ℕ × ℕ) : ℤ :=
  s.leftFrequency * ((pair.2 * MovingSlotReversal.naturalProduct value s.rightSlots : ℕ) : ℤ) -
    s.rightFrequency * ((pair.1 * MovingSlotReversal.naturalProduct value s.leftSlots : ℕ) : ℤ)

/-- All recursive exclusions are exactly the exclusions in the recorded
occurrence list, evaluated along their actual natural paths. -/
theorem MovingSlotData.squareTests_iff_occurrences {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    T.PrimeSquareTests value XL XR ↔
      ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
        ¬ (value i : ℤ) ^ 2 ∣ o.current.integerNumerator value
          (movingSlotNaturalPath value o.path (XL, XR)) := by
  induction T generalizing XL XR with
  | leaf => simp [PrimeSquareTests, occurrences]
  | @node n s CL CR U left right ihL ihR =>
    let step := MovingSlotData.step s CL CR U left right
    let p := (step false).naturalPivot value XL XR
    have hl := ihL p XL
    have hr := ihR p XR
    constructor
    · rintro ⟨hroot, hleft, hright⟩ o ho i hi
      rcases List.mem_cons.mp ho with ho | ho
      · subst o
        exact hroot (value i) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      · rcases List.mem_append.mp ho with ho | ho
        · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
          have h := hl.mp hleft o' hmem i hi
          simpa only [MovingSlotOccurrence.extend, movingSlotNaturalPath_append,
            movingSlotNaturalPath, MovingSlotReversal.naturalStep, p, step, MovingSlotReversal.naturalPivot,
            MovingSlotData.step, ite_true] using h
        · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
          have h := hr.mp hright o' hmem i hi
          simpa only [MovingSlotOccurrence.extend, movingSlotNaturalPath_append,
            movingSlotNaturalPath, MovingSlotReversal.naturalStep, p, step, MovingSlotReversal.naturalPivot,
            MovingSlotData.step, Bool.false_eq_true, ite_false] using h
    · intro h
      refine ⟨?_, hl.mpr ?_, hr.mpr ?_⟩
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        exact h ⟨n + 1, step false, []⟩ (List.mem_cons_self) i hi
      · intro o ho i hi
        have hh := h (o.extend (step true))
          (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩))) i hi
        simpa only [MovingSlotOccurrence.extend, movingSlotNaturalPath_append,
          movingSlotNaturalPath, MovingSlotReversal.naturalStep, p, step, MovingSlotReversal.naturalPivot,
          MovingSlotData.step, ite_true] using hh
      · intro o ho i hi
        have hh := h (o.extend (step false))
          (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))) i hi
        simpa only [MovingSlotOccurrence.extend, movingSlotNaturalPath_append,
          movingSlotNaturalPath, MovingSlotReversal.naturalStep, p, step, MovingSlotReversal.naturalPivot,
          MovingSlotData.step, Bool.false_eq_true, ite_false] using hh

/-- A current compensation slot belongs to the type immediately below the
occurrence, including when a prime represents multiple occurrences. -/
theorem MovingSlotData.occurrence_compensation_level {σ : Type*} (tier : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.Levels tier) :
    ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots, tier i < o.level := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR U left right ihL ihR =>
    intro o ho i hi
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      have he := hT.2.2.1 i hi
      change tier i < n + 1
      omega
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
        exact ihL hT.2.2.2.1 o' hmem i hi
      · obtain ⟨o', hmem, rfl⟩ := List.mem_map.mp ho
        exact ihR hT.2.2.2.2 o' hmem i hi

theorem MovingSlotData.occurrences_length {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) : T.occurrences.length = 2 ^ n - 1 := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR U left right ihL ihR =>
    simp only [occurrences, List.length_cons, List.length_append, List.length_map, ihL, ihR,
      pow_succ]
    have hpos : 0 < 2 ^ n := pow_pos (by decide) n
    omega

/-- The full recursive support has only linear equations at the original
pair of giants modulo the current compensation-prime squares. -/
theorem MovingSlotData.squareTests_iff_lines {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hfreq : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) :
    T.PrimeSquareTests value XL XR ↔
      ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
        let φ := MovingSlotReversal.naturalReduction (value i ^ 2) value
        φ (movingSlotLine o.path o.current).a * (XL : ZMod (value i ^ 2)) +
          φ (movingSlotLine o.path o.current).b * (XR : ZMod (value i ^ 2)) ≠ 0 := by
  rw [T.squareTests_iff_occurrences value XL XR]
  apply forall₂_congr
  intro o ho
  apply forall₂_congr
  intro i hi
  let : Fact (value i).Prime := ⟨hprime i⟩
  have hu := T.occurrence_units_of_prime_types tier value hprime hdisjoint hlevels
    o ho i (T.occurrence_compensation_level tier hlevels o ho i hi) (hfreq i)
  have hv := (T.occurrence_integral value XL XR hI o ho).1
  exact (not_congr (movingSlotLine_square_zero_iff value o.path o.current XL XR hv
    (fun s hs => (hu.1 s hs).2.2))).symm

/-- Full original pairwise support reduces to top coprimality and precisely
these square-line exclusions. The arithmetic and frequency guards are kept. -/
theorem MovingSlotData.fullPairwise_iff_lines {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hcoh : T.RegularCoherent) (hc : T.CompensationPrimeData value)
    (hf : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR)
    (hcross : T.CrossFrequencyUnits value XL XR) :
    T.FullPairwise value XL XR ↔ T.CurrentPairwise value XL XR ∧
      ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
        let φ := MovingSlotReversal.naturalReduction (value i ^ 2) value
        φ (movingSlotLine o.path o.current).a * (XL : ZMod (value i ^ 2)) +
          φ (movingSlotLine o.path o.current).b * (XR : ZMod (value i ^ 2)) ≠ 0 := by
  rw [T.fullPairwise_iff_squareTests value hcoh hc XL XR hI hcross,
    T.squareTests_iff_lines tier value hprime hdisjoint hlevels hf XL XR hI]

end Ostmann

end OAI
