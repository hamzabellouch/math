import OAI.NumberTheory.Ostmann.Arithmetic.BulkSlotFieldBridge

namespace OAI

/-! # One rational diagram for all bulk replacements of fixed nonbulk data -/

namespace Ostmann
open scoped Classical ComplexConjugate

theorem buildMovingSlotData_frozen_field_diagram {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n : ℕ) (t : FrequencyTree ℤ n)
    (small : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (hfreq : movingGiantFrequencyUnits q n t)
    (hsmall : ((treeLeafProduct n (movingSlotValues base n small) : ℕ) : ZMod q) ≠ 0)
    (hsamples : (samples.values base).UnitsAt q) :
    ∃ (U : (ZMod q)ˣ) (R : RationalTreeData (ZMod q)ˣ n U),
      ∀ (value : σ → ℕ), movingSlotValues value n small = movingSlotValues base n small →
      samples.values value = samples.values base →
      ∀ (g : ZMod q → ℂ) (D A B : (ZMod q)ˣ)
        (bulk : TreeLeafTuple (List σ) n) (z : TreeLeafTuple (ZMod q)ˣ n),
      TreeNaturalLift n (movingSlotValues value n bulk) z →
      movingModularSpectator value q g D (buildMovingSlotData n t small bulk samples) A B =
        rationalTreeAmplitude g D R A B (transferConjugations n false) z := by
  let T := buildMovingGiantTree n t (movingSlotValues base n small) (samples.values base)
  have hT : T.UnitsAt q := buildMovingGiantTree_units t _ _ hfreq hsmall hsamples
  obtain ⟨U, R, _, _, hR⟩ := T.exists_field_diagram hT
  refine ⟨U, R, ?_⟩
  intro value hv hs g D A B bulk z hz
  rw [buildMovingSlotData_modular_spectator value g D n t small bulk samples A B z hz,
    hv, hs]
  exact hR g D A B z false

/-- The same pair of diagrams works simultaneously for every actual bulk
tuple with the fixed small leaves and fixed internal samples. -/
theorem moving_field_pair_frozen_diagrams {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ b, movingGiantFrequencyUnits q n (t b))
    (hsmall : ∀ b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D A B : Bool → (ZMod q)ˣ) :
    ∃ d : Bool → SpectatorDiagram q n,
      (∀ b, (d b).conjugations = transferConjugations n false) ∧
      ∀ (value : σ → ℕ),
        (∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b)) →
        (∀ b, (samples b).values value = (samples b).values base) →
      ∀ (g : ZMod q → ℂ) (bulk : Bool → TreeLeafTuple (List σ) n)
        (z : Bool → TreeLeafTuple (ZMod q)ˣ n),
        (∀ b, TreeNaturalLift n (movingSlotValues value n (bulk b)) (z b)) →
        movingModularSpectator value q g (D false)
          (buildMovingSlotData n (t false) (small false) (bulk false) (samples false)) (A false) (B false) *
          conj (movingModularSpectator value q g (D true)
            (buildMovingSlotData n (t true) (small true) (bulk true) (samples true)) (A true) (B true)) =
          (d false).value g (z false) * conj ((d true).value g (z true)) := by
  have h b := buildMovingSlotData_frozen_field_diagram base n (t b) (small b) (samples b)
    (hfreq b) (hsmall b) (hsamples b)
  choose U R hR using h
  let d (b : Bool) : SpectatorDiagram q n :=
    ⟨D b, U b, R b, A b, B b, transferConjugations n false⟩
  refine ⟨d, fun _ => rfl, ?_⟩
  intro value hv hs g bulk z hz
  rw [hR false value (hv false) (hs false) g (D false) (A false) (B false) (bulk false) (z false) (hz false),
    hR true value (hv true) (hs true) g (D true) (A true) (B true) (bulk true) (z true) (hz true)]
  rfl

theorem moving_field_pair_frozen_bulk_slots {σ : Type*} {q : ℕ} [Fact q.Prime]
    (base : σ → ℕ) (n m : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ b, movingGiantFrequencyUnits q n (t b))
    (hsmall : ∀ b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D A B : Bool → (ZMod q)ˣ) :
    ∃ d : Bool → SpectatorDiagram q n,
      (∀ b, (d b).conjugations = transferConjugations n false) ∧
      ∀ (value : σ → ℕ),
        (∀ b, movingSlotValues value n (small b) = movingSlotValues base n (small b)) →
        (∀ b, (samples b).values value = (samples b).values base) →
      ∀ (g : ZMod q → ℂ) (slot : TreeLeafIndex n × Fin m → σ)
        (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ),
        (∀ j, (value (slot j) : ZMod q) = (z j : ZMod q)) →
        movingModularSpectator value q g (D false)
          (buildMovingSlotData n (t false) (small false) (bulkSlotLeaves n m slot) (samples false))
          (A false) (B false) *
          conj (movingModularSpectator value q g (D true)
            (buildMovingSlotData n (t true) (small true)
              (bulkSlotLeaves n m (slot ∘ e.symm)) (samples true)) (A true) (B true)) =
          (d false).bulkValue g z * conj ((d true).bulkValue g (z ∘ e.symm)) := by
  obtain ⟨d, hd, he⟩ := moving_field_pair_frozen_diagrams base n t small samples
    hfreq hsmall hsamples D A B
  refine ⟨d, hd, ?_⟩
  intro value hv hs g slot e z hz
  let bulk := fun b : Bool => if b then bulkSlotLeaves n m (slot ∘ e.symm) else bulkSlotLeaves n m slot
  let Z := fun b : Bool => if b then
    (treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct (z ∘ e.symm)) else
    (treeLeafTupleEquiv (ZMod q)ˣ n).symm (bulkBlockProduct z)
  have hlift (b : Bool) : TreeNaturalLift n (movingSlotValues value n (bulk b)) (Z b) := by
    cases b
    · exact bulkSlotLeaves_naturalLift value n m slot z hz
    · exact bulkSlotLeaves_naturalLift value n m (slot ∘ e.symm) (z ∘ e.symm) (fun j => hz (e.symm j))
  exact he value hv hs g bulk Z hlift

end Ostmann

end OAI
