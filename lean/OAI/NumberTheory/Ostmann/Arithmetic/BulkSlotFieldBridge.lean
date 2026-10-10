import OAI.NumberTheory.Ostmann.Arithmetic.MovingFieldDiagram
import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkComparison

namespace OAI

/-! # The original labelled bulk slots produce the quartet leaf arrays -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem treeNaturalLift_iff_indexed {q : ℕ} (n : ℕ)
    (x : TreeLeafTuple ℕ n) (y : TreeLeafTuple (ZMod q)ˣ n) :
    TreeNaturalLift n x y ↔ ∀ j : TreeLeafIndex n,
      (treeLeafTupleEquiv ℕ n x j : ZMod q) = (treeLeafTupleEquiv (ZMod q)ˣ n y j : ZMod q) := by
  induction n with
  | zero =>
    constructor
    · intro h _; exact h
    · intro h; exact h ()
  | succ n ih =>
    constructor
    · rintro ⟨hL, hR⟩ (j | j)
      · exact (ih x.1 y.1).mp hL j
      · exact (ih x.2 y.2).mp hR j
    · intro h
      exact ⟨(ih x.1 y.1).mpr (fun j => h (.inl j)),
        (ih x.2 y.2).mpr (fun j => h (.inr j))⟩

theorem movingSlotValues_indexed {σ : Type*} (value : σ → ℕ) (n : ℕ)
    (s : TreeLeafTuple (List σ) n) (j : TreeLeafIndex n) :
    treeLeafTupleEquiv ℕ n (movingSlotValues value n s) j =
      MovingSlotReversal.naturalProduct value (treeLeafTupleEquiv (List σ) n s j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases j with
    | inl j => exact ih s.1 j
    | inr j => exact ih s.2 j

noncomputable def bulkSlotLeaves {σ : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → σ) : TreeLeafTuple (List σ) n :=
  (treeLeafTupleEquiv (List σ) n).symm (fun j => List.ofFn (fun i => slot (j, i)))

theorem bulkSlotLeaves_naturalLift {σ : Type*} {q : ℕ} (value : σ → ℕ)
    (n m : ℕ) (slot : TreeLeafIndex n × Fin m → σ)
    (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (hz : ∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) :
    TreeNaturalLift n (movingSlotValues value n (bulkSlotLeaves n m slot))
      ((treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct z)) := by
  rw [treeNaturalLift_iff_indexed]
  intro j
  rw [movingSlotValues_indexed]
  simp only [bulkSlotLeaves, Equiv.apply_symm_apply, MovingSlotReversal.naturalProduct,
    List.map_ofFn, List.prod_ofFn, Nat.cast_prod, bulkBlockProduct, Units.coe_prod]
  exact Finset.prod_congr rfl (fun i _ => hz (j, i))

/-- The same labelled slot map is used in both histories, with precisely the
specified permutation. The rational diagrams are chosen before the bulk primes. -/
theorem moving_field_pair_bulk_slots {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ side, movingGiantFrequencyUnits q n (t side))
    (hsmall : ∀ side, ((treeLeafProduct n (movingSlotValues value n (small side)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ side, ((samples side).values value).UnitsAt q)
    (D A B : Bool → (ZMod q)ˣ) :
    ∃ d : Bool → SpectatorDiagram q n,
      (∀ side, (d side).conjugations = transferConjugations n false) ∧
      ∀ (g : ZMod q → ℂ) (slot : TreeLeafIndex n × Fin m → σ)
        (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ),
        (∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) →
        movingModularSpectator value q g (D false)
          (buildMovingSlotData n (t false) (small false) (bulkSlotLeaves n m slot) (samples false))
          (A false) (B false) *
          conj (movingModularSpectator value q g (D true)
            (buildMovingSlotData n (t true) (small true) (bulkSlotLeaves n m (slot ∘ e.symm)) (samples true))
            (A true) (B true)) =
        (d false).bulkValue g z * conj ((d true).bulkValue g (z ∘ e.symm)) := by
  obtain ⟨d, hc, hd⟩ := moving_field_pair_diagrams value n t small samples hfreq hsmall hsamples D A B
  refine ⟨d, hc, ?_⟩
  intro g slot e z hz
  let bulk := fun b : Bool => if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot
  let Z := fun b : Bool => if b then (treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct (z ∘ e.symm))
    else (treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct z)
  have hlift (b : Bool) : TreeNaturalLift n (movingSlotValues value n (bulk b)) (Z b) := by
    cases b
    · exact bulkSlotLeaves_naturalLift value n m slot z hz
    · exact bulkSlotLeaves_naturalLift value n m (slot ∘ e.symm) (z ∘ e.symm) (fun j => hz (e.symm j))
  exact hd g bulk Z hlift

end Ostmann

end OAI
