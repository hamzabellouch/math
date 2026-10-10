import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSlots
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotRealization

namespace OAI

/-! # Unit coefficients for the actual sampled occurrence paths -/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.Frequencies {σ : Type*} (s : MovingSlotReversal σ)
    (P : ℤ → Prop) : Prop := P s.leftFrequency ∧ P s.rightFrequency ∧ P s.rootFrequency

def MovingSlotData.Frequencies {σ : Type*} (P : ℤ → Prop) : {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf s _ => P s
  | _, .node s _ _ _ left right => P s ∧ left.Frequencies P ∧ right.Frequencies P

theorem MovingSlotData.Frequencies.root {σ : Type*} {P : ℤ → Prop} {n : ℕ}
    {T : MovingSlotData σ n} (h : T.Frequencies P) : P T.frequency := by
  cases T with
  | leaf => exact h
  | node => exact h.1

theorem MovingSlotData.occurrence_frequencies {σ : Type*} (P : ℤ → Prop) {n : ℕ}
    (T : MovingSlotData σ n) (hT : T.Frequencies P) :
    ∀ o ∈ T.occurrences, o.current.Frequencies P ∧ ∀ s ∈ o.path, s.Frequencies P := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    intro o ho
    have hb (b : Bool) : (step s CL CR u left right b).Frequencies P :=
      ⟨hT.2.1.root, hT.2.2.root, hT.1⟩
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      exact ⟨hb false, by simp⟩
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihL hT.2.1 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb true
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihR hT.2.2 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb false

/-- The current compensation primes can repeat within their equality pattern.
Only their disjointness from the earlier coefficient types is used here. -/
theorem MovingSlotData.occurrence_units {σ : Type*} {q : ℕ} [Fact q.Prime]
    (tier : σ → ℕ) (value : σ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hlevels : T.Levels tier) (hfreq : T.Frequencies (fun s => (s : ZMod q) ≠ 0))
    (o : MovingSlotOccurrence σ) (ho : o ∈ T.occurrences)
    (hcop : ∀ i, o.level ≤ tier i → (value i).Coprime q) :
    (∀ s ∈ o.path,
      MovingSlotReversal.naturalReduction q value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value s.polynomial.u ≠ 0) ∧
    MovingSlotReversal.naturalReduction q value o.current.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction q value o.current.polynomial.w ≠ 0 := by
  have hl := (T.occurrence_bounds tier hlevels o ho).2.2
  have hf := T.occurrence_frequencies _ hfreq o ho
  have hc (s : ℤ) (slots : List σ) (hs : (s : ZMod q) ≠ 0)
      (hslots : ∀ i ∈ slots, o.level ≤ tier i) :
      MovingSlotReversal.naturalReduction q value (movingSlotCoefficient s slots) ≠ 0 := by
    simpa only [MovingSlotReversal.naturalReduction] using
      movingSlotCoefficient_ne_zero (fun i => (value i : ZMod q)) s slots hs
        (fun i hi => ((ZMod.isUnit_iff_coprime _ _).mpr (hcop i (hslots i hi))).ne_zero)
  refine ⟨?_, hc _ _ hf.1.1 hl.2.2, hc _ _ hf.1.2.1 hl.2.1⟩
  intro s hs
  exact ⟨hc _ _ (hf.2 s hs).1 (hl.1 s hs).2.1,
    hc _ _ (hf.2 s hs).2.1 (hl.1 s hs).1,
    hc _ _ (hf.2 s hs).2.2 (hl.1 s hs).2.2⟩

/-- Disjoint prime types discharge all denominator and nonzero-row conditions
at every occurrence of the selected representative. -/
theorem MovingSlotData.occurrence_units_of_prime_types {σ : Type*}
    (tier : σ → ℕ) (value : σ → ℕ) (hprime : ∀ i, (value i).Prime)
    (hdisjoint : ∀ i j, tier i ≠ tier j → value i ≠ value j)
    {n : ℕ} (T : MovingSlotData σ n) (hlevels : T.Levels tier)
    (o : MovingSlotOccurrence σ) (ho : o ∈ T.occurrences) (rep : σ)
    (hrep : tier rep < o.level)
    (hfreq : T.Frequencies (fun s => (s : ZMod (value rep)) ≠ 0)) :
    (∀ s ∈ o.path,
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.w ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value s.polynomial.u ≠ 0) ∧
    MovingSlotReversal.naturalReduction (value rep) value o.current.polynomial.v ≠ 0 ∧
      MovingSlotReversal.naturalReduction (value rep) value o.current.polynomial.w ≠ 0 := by
  let : Fact (value rep).Prime := ⟨hprime rep⟩
  apply T.occurrence_units tier value hlevels hfreq o ho
  intro i hi
  exact (Nat.coprime_primes (hprime i) (hprime rep)).mpr
    (hdisjoint i rep (by omega))

theorem buildMovingSlotData_frequencyUnits {σ : Type*} {q : ℕ} (n : ℕ)
    (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (samples : MovingSampleSlots σ n) (h : movingGiantFrequencyUnits q n t) :
    (buildMovingSlotData n t small bulk samples).Frequencies (fun s => (s : ZMod q) ≠ 0) := by
  induction samples with
  | leaf => exact h
  | @node n samples left right ihL ihR =>
    exact ⟨h.1, ihL _ _ _ h.2.1, ihR _ _ _ h.2.2⟩

end Ostmann

end OAI
