import OAI.NumberTheory.Ostmann.Arithmetic.MovingLineComposition

namespace OAI

/-! # The internal-prime gate on the original top giant pair -/

namespace Ostmann
open scoped Classical

noncomputable def movingPrimeLineSupport {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (x y : ℤ) : Prop :=
  ∀ o ∈ T.occurrences, ∀ i ∈ o.current.compensationSlots,
    let φ := MovingSlotReversal.naturalReduction (value i) value
    φ (movingSlotLine o.path o.current).a * (x : ZMod (value i)) +
      φ (movingSlotLine o.path o.current).b * (y : ZMod (value i)) = 0

theorem movingPrimeLineSupport_leaf {σ : Type*} (value : σ → ℕ)
    (s : ℤ) (C : List σ) (x y : ℤ) :
    movingPrimeLineSupport value (.leaf s C) x y := by
  simp [movingPrimeLineSupport, MovingSlotData.occurrences]

theorem movingPrimeLineSupport_root {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (x y : ℤ)
    (h : movingPrimeLineSupport value (.node s CL CR U left right) x y) :
    ∀ i ∈ U, (value i : ℤ) ∣
      (MovingSlotData.step s CL CR U left right false).signedNumerator value x y := by
  intro i hi
  have he := h ⟨n + 1, MovingSlotData.step s CL CR U left right false, []⟩
    List.mem_cons_self i hi
  have hh : ((MovingSlotData.step s CL CR U left right false).signedNumerator value x y :
      ZMod (value i)) = 0 := by
    dsimp only at he
    rw [movingSlotLine_eval] at he
    simpa only [MovingSlotReversal.naturalReduction, MovingSlotReversal.signedNumerator,
      MovingSlotReversal.polynomial, MovingSlotReversal.coefficient_nat_eval,
      PolynomialGiantRows.evalNumerator, movingPolynomialAncestors, List.map_nil,
      PolynomialGiantRows.identity, GiantRows.identity, map_one, map_zero, one_mul,
      zero_mul, mul_zero, mul_one, add_zero, zero_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      mul_assoc, mul_comm, mul_left_comm] using he
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh

/-- Decomposition of the top-coordinate line gate after just the current
integer relation is known; descendant integrality is not an assumption. -/
theorem movingPrimeLineSupport_node {σ : Type*} (value : σ → ℕ)
    (hprime : ∀ i, (value i).Prime) {n : ℕ}
    (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n) (x y p : ℤ)
    (hrel : (MovingSlotData.step s CL CR U left right false).signedNumerator value x y =
      s * (MovingSlotReversal.naturalProduct value U : ℤ) * p)
    (hUL : ∀ o ∈ left.occurrences, ∀ i ∈ o.current.compensationSlots,
      MovingSlotReversal.naturalReduction (value i) value
        (MovingSlotData.step s CL CR U left right true).polynomial.u ≠ 0)
    (hUR : ∀ o ∈ right.occurrences, ∀ i ∈ o.current.compensationSlots,
      MovingSlotReversal.naturalReduction (value i) value
        (MovingSlotData.step s CL CR U left right false).polynomial.u ≠ 0) :
    movingPrimeLineSupport value (.node s CL CR U left right) x y ↔
      (∀ i ∈ U, (value i : ℤ) ∣
        (MovingSlotData.step s CL CR U left right false).signedNumerator value x y) ∧
      movingPrimeLineSupport value left p x ∧ movingPrimeLineSupport value right p y := by
  let step := MovingSlotData.step s CL CR U left right
  have hleft (o : MovingSlotOccurrence σ) (ho : o ∈ left.occurrences)
      (i : σ) (hi : i ∈ o.current.compensationSlots) :
      let φ := MovingSlotReversal.naturalReduction (value i) value
      φ (movingSlotLine (o.path ++ [step true]) o.current).a * (x : ZMod (value i)) +
          φ (movingSlotLine (o.path ++ [step true]) o.current).b * (y : ZMod (value i)) = 0 ↔
        φ (movingSlotLine o.path o.current).a * (p : ZMod (value i)) +
          φ (movingSlotLine o.path o.current).b * (x : ZMod (value i)) = 0 := by
    let : Fact (value i).Prime := ⟨hprime i⟩
    exact movingSlotLine_append_singleton_zero_iff value o.path o.current (step true)
      x y p hrel (hUL o ho i hi)
  have hright (o : MovingSlotOccurrence σ) (ho : o ∈ right.occurrences)
      (i : σ) (hi : i ∈ o.current.compensationSlots) :
      let φ := MovingSlotReversal.naturalReduction (value i) value
      φ (movingSlotLine (o.path ++ [step false]) o.current).a * (x : ZMod (value i)) +
          φ (movingSlotLine (o.path ++ [step false]) o.current).b * (y : ZMod (value i)) = 0 ↔
        φ (movingSlotLine o.path o.current).a * (p : ZMod (value i)) +
          φ (movingSlotLine o.path o.current).b * (y : ZMod (value i)) = 0 := by
    let : Fact (value i).Prime := ⟨hprime i⟩
    exact movingSlotLine_append_singleton_zero_iff value o.path o.current (step false)
      x y p hrel (hUR o ho i hi)
  constructor
  · intro h
    refine ⟨movingPrimeLineSupport_root value s CL CR U left right x y h, ?_, ?_⟩
    · intro o ho i hi
      apply (hleft o ho i hi).mp
      exact h (o.extend (step true)) (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩))) i hi
    · intro o ho i hi
      apply (hright o ho i hi).mp
      exact h (o.extend (step false)) (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩))) i hi
  · rintro ⟨hroot, hL, hR⟩ o ho i hi
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (value i)).mpr (hroot i hi)
      dsimp only
      rw [movingSlotLine_eval]
      simpa only [MovingSlotReversal.naturalReduction, MovingSlotReversal.signedNumerator,
        MovingSlotReversal.polynomial, MovingSlotReversal.coefficient_nat_eval,
        PolynomialGiantRows.evalNumerator, movingPolynomialAncestors, List.map_nil,
        PolynomialGiantRows.identity, GiantRows.identity, map_one, map_zero, one_mul,
        zero_mul, mul_zero, mul_one, add_zero, zero_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
        mul_assoc, mul_comm, mul_left_comm] using hz
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact (hleft o' ho' i hi).mpr (hL o' ho' i hi)
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact (hright o' ho' i hi).mpr (hR o' ho' i hi)

theorem MovingSlotData.compensation_ancestor_unit {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (hf : ∀ i, T.Frequencies (fun s => (s : ZMod (value i)) ≠ 0))
    (o : MovingSlotOccurrence σ) (ho : o ∈ T.occurrences)
    (i : σ) (hi : i ∈ o.current.compensationSlots) :
    ∀ root ∈ o.path,
      MovingSlotReversal.naturalReduction (value i) value root.polynomial.u ≠ 0 := by
  have h := T.occurrence_units_of_prime_types tier value hprime hdisjoint hlevels o ho i
    (T.occurrence_compensation_level tier hlevels o ho i hi) (hf i)
  exact fun root hr => (h.1 root hr).2.2

theorem movingPrimeLineSupport_node_of_levels {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (s : ℤ) (CL CR U : List σ) (left right : MovingSlotData σ n)
    (hlevels : (MovingSlotData.node s CL CR U left right).Levels tier)
    (hf : ∀ i, (MovingSlotData.node s CL CR U left right).Frequencies
      (fun f => (f : ZMod (value i)) ≠ 0)) (x y p : ℤ)
    (hrel : (MovingSlotData.step s CL CR U left right false).signedNumerator value x y =
      s * (MovingSlotReversal.naturalProduct value U : ℤ) * p) :
    movingPrimeLineSupport value (.node s CL CR U left right) x y ↔
      (∀ i ∈ U, (value i : ℤ) ∣
        (MovingSlotData.step s CL CR U left right false).signedNumerator value x y) ∧
      movingPrimeLineSupport value left p x ∧ movingPrimeLineSupport value right p y := by
  apply movingPrimeLineSupport_node value hprime s CL CR U left right x y p hrel
  · intro o ho i hi
    exact (MovingSlotData.node s CL CR U left right).compensation_ancestor_unit
      tier value hprime hdisjoint hlevels hf (o.extend (MovingSlotData.step s CL CR U left right true))
      (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩)))
      i hi _ (by simp [MovingSlotOccurrence.extend])
  · intro o ho i hi
    exact (MovingSlotData.node s CL CR U left right).compensation_ancestor_unit
      tier value hprime hdisjoint hlevels hf (o.extend (MovingSlotData.step s CL CR U left right false))
      (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.mpr ⟨o, ho, rfl⟩)))
      i hi _ (by simp [MovingSlotOccurrence.extend])

end Ostmann

end OAI
