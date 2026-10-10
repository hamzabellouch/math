import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleIntegrality

namespace OAI

/-! # Every occurrence follows the actual reconstructed integer path -/

namespace Ostmann
open scoped Classical

theorem movingSlotNaturalPath_append {σ : Type*} (value : σ → ℕ)
    (a b : List (MovingSlotReversal σ)) (pair : ℕ × ℕ) :
    movingSlotNaturalPath value (a ++ b) pair =
      movingSlotNaturalPath value a (movingSlotNaturalPath value b pair) := by
  induction a with
  | nil => rfl
  | cons s a ih => simp only [List.cons_append, movingSlotNaturalPath, ih]

theorem movingSlotPathIntegral_append {σ : Type*} (value : σ → ℕ)
    (a b : List (MovingSlotReversal σ)) (pair : ℕ × ℕ) :
    MovingSlotPathIntegral value (a ++ b) pair ↔
      MovingSlotPathIntegral value b pair ∧
        MovingSlotPathIntegral value a (movingSlotNaturalPath value b pair) := by
  induction a with
  | nil => simp [MovingSlotPathIntegral]
  | cons s a ih =>
    simp only [List.cons_append, MovingSlotPathIntegral, movingSlotNaturalPath_append, ih, and_assoc]

/-- The integral support at a tree yields all the local integer equalities
used in the polynomial line interpretation. This is constructive for every
listed occurrence, including both child orders. -/
theorem MovingSlotData.occurrence_integral {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ) (hT : T.Integral value XL XR) :
    ∀ o ∈ T.occurrences,
      MovingSlotPathIntegral value o.path (XL, XR) ∧
      o.current.IntegralAt value (movingSlotNaturalPath value o.path (XL, XR)) := by
  induction T generalizing XL XR with
  | leaf s regular => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right
    let p := (step false).naturalPivot value XL XR
    have hroot : (step false).IntegralAt value (XL, XR) := hT.1
    have htrue : (step true).IntegralAt value (XL, XR) := hroot
    have hleft := ihL p XL hT.2.1
    have hright := ihR p XR hT.2.2
    intro o ho
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      exact ⟨trivial, hroot⟩
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hc⟩ := hleft o' ho'
        have hpair : movingSlotNaturalPath value [step true] (XL, XR) = (p, XL) := rfl
        constructor
        · change MovingSlotPathIntegral value (o'.path ++ [step true]) (XL, XR)
          rw [movingSlotPathIntegral_append, hpair]
          exact ⟨⟨trivial, htrue⟩, hp⟩
        · change o'.current.IntegralAt value (movingSlotNaturalPath value (o'.path ++ [step true]) (XL, XR))
          rw [movingSlotNaturalPath_append, hpair]
          exact hc
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨hp, hc⟩ := hright o' ho'
        have hpair : movingSlotNaturalPath value [step false] (XL, XR) = (p, XR) := rfl
        constructor
        · change MovingSlotPathIntegral value (o'.path ++ [step false]) (XL, XR)
          rw [movingSlotPathIntegral_append, hpair]
          exact ⟨⟨trivial, hroot⟩, hp⟩
        · change o'.current.IntegralAt value (movingSlotNaturalPath value (o'.path ++ [step false]) (XL, XR))
          rw [movingSlotNaturalPath_append, hpair]
          exact hc

theorem buildMovingSlotData_occurrence_integral {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (XL XR : ℕ)
    (hT : (buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value)).Integral
      XL XR (movingSlotValues value n bulk))
    (o : MovingSlotOccurrence σ)
    (ho : o ∈ (buildMovingSlotData n t small bulk samples).occurrences) :
    MovingSlotPathIntegral value o.path (XL, XR) ∧
      o.current.IntegralAt value (movingSlotNaturalPath value o.path (XL, XR)) :=
  MovingSlotData.occurrence_integral value _ XL XR
    ((buildMovingSlotData_integral value n t small bulk samples XL XR).mpr hT) o ho

end Ostmann

end OAI
