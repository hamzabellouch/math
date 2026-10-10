import OAI.NumberTheory.Ostmann.Arithmetic.MovingPolynomialRelabel
import OAI.NumberTheory.Ostmann.Arithmetic.MovingInternalBaseAverage

namespace OAI

/-! # Actual internal-prime line systems commute with slot relabelling -/

namespace Ostmann
open scoped Classical

def MovingSlotOccurrence.map {σ τ : Type*} (f : σ → τ)
    (o : MovingSlotOccurrence σ) : MovingSlotOccurrence τ :=
  ⟨o.level, o.current.map f, o.path.map (MovingSlotReversal.map f)⟩

theorem MovingSlotOccurrence.map_extend {σ τ : Type*} (f : σ → τ)
    (o : MovingSlotOccurrence σ) (s : MovingSlotReversal σ) :
    (o.extend s).map f = (o.map f).extend (s.map f) := by
  simp only [map, extend, List.map_append, List.map_singleton]

theorem MovingSlotData.occurrences_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : MovingSlotData σ n) :
    (T.map f).occurrences = T.occurrences.map (MovingSlotOccurrence.map f) := by
  induction T with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.map, occurrences, step_map, ihL, ihR,
      List.map_cons, List.map_append, List.map_map, Function.comp_def,
      MovingSlotOccurrence.map, MovingSlotOccurrence.extend, List.map_nil]

/-- The finite index of occurrences is only bookkeeping: the event itself is
exactly the conjunction over the original compensation slots. -/
theorem movingPrimeLineSystem_iff {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) (x y : ZMod p) :
    (∀ j : MovingPrimeOccurrences value T p,
      let L := movingPrimeOccurrenceLine value T p j
      let φ := MovingSlotReversal.naturalReduction p value
      φ L.a * x + φ L.b * y = 0) ↔
    (∀ side o, o ∈ (T side).occurrences →
      ∀ i ∈ o.current.compensationSlots, value i = p →
      let L := movingSlotLine o.path o.current
      let φ := MovingSlotReversal.naturalReduction p value
      φ L.a * x + φ L.b * y = 0) := by
  constructor
  · intro h side o ho i hi hv
    obtain ⟨k, hk, hko⟩ := List.mem_iff_getElem.mp ho
    let j : MovingPrimeOccurrences value T p :=
      ⟨side, ⟨⟨k, hk⟩, by simpa only [List.get_eq_getElem, hko] using ⟨i, hi, hv⟩⟩⟩
    simpa only [movingPrimeOccurrenceLine, movingPrimeOccurrence, j, List.get_eq_getElem, hko] using h j
  · intro h j
    obtain ⟨i, hi, hv⟩ := j.2.property
    exact h j.1 _ (List.get_mem _ _) i hi hv

theorem movingSlotLine_natural_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) (p : ℕ) (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) :
    let L := movingSlotLine path current
    let L' := movingSlotLine (path.map (MovingSlotReversal.map f)) (current.map f)
    let φ := MovingSlotReversal.naturalReduction p (value ∘ f)
    let φ' := MovingSlotReversal.naturalReduction p value
    φ' L'.a = φ L.a ∧ φ' L'.b = φ L.b := by
  have h := movingSlotLine_map f path current
  dsimp only
  rw [h.1, h.2.1]
  simp only [MovingSlotReversal.naturalReduction, MvPolynomial.eval₂Hom_rename,
    Function.comp_def, and_self]

theorem movingPrimeLineSystem_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n) (p : ℕ)
    (x y : ZMod p) :
    (∀ j : MovingPrimeOccurrences value (fun side => (T side).map f) p,
      let L := movingPrimeOccurrenceLine value (fun side => (T side).map f) p j
      let φ := MovingSlotReversal.naturalReduction p value
      φ L.a * x + φ L.b * y = 0) ↔
    (∀ j : MovingPrimeOccurrences (value ∘ f) T p,
      let L := movingPrimeOccurrenceLine (value ∘ f) T p j
      let φ := MovingSlotReversal.naturalReduction p (value ∘ f)
      φ L.a * x + φ L.b * y = 0) := by
  rw [movingPrimeLineSystem_iff, movingPrimeLineSystem_iff]
  constructor
  · intro h side o ho i hi hv
    have he := h side (o.map f) (by rw [MovingSlotData.occurrences_map]; exact List.mem_map.mpr ⟨o, ho, rfl⟩)
      (f i) (List.mem_map.mpr ⟨i, hi, rfl⟩) hv
    have hl := movingSlotLine_natural_map f value p o.path o.current
    change _ = 0 at he
    simpa only [MovingSlotOccurrence.map, hl.1, hl.2] using he
  · intro h side o ho i hi hv
    rw [MovingSlotData.occurrences_map] at ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    have he := h side o' ho' i' hi' hv
    have hl := movingSlotLine_natural_map f value p o'.path o'.current
    change _ = 0
    simpa only [MovingSlotOccurrence.map, hl.1, hl.2] using he

theorem movingInternalBaseProbability_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) {n : ℕ} (T : Bool → MovingSlotData σ n)
    (p : ℕ) [Fact p.Prime] :
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value (fun side => (T side).map f) p j).a)
      (fun j => MovingSlotReversal.naturalReduction p value
        (movingPrimeOccurrenceLine value (fun side => (T side).map f) p j).b) =
    internalLineProbability true
      (fun j => MovingSlotReversal.naturalReduction p (value ∘ f)
        (movingPrimeOccurrenceLine (value ∘ f) T p j).a)
      (fun j => MovingSlotReversal.naturalReduction p (value ∘ f)
        (movingPrimeOccurrenceLine (value ∘ f) T p j).b) := by
  unfold internalLineProbability
  simp only [ite_true, ← Nat.card_eq_fintype_card]
  apply congrArg (fun k : ℕ => (k : ℝ) / Nat.card (ZMod p × (ZMod p)ˣ))
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun z : ZMod p × (ZMod p)ˣ =>
    movingPrimeLineSystem_map f value T p z.1 z.2))

end Ostmann

end OAI
