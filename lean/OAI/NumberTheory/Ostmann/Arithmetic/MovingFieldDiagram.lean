import OAI.NumberTheory.Ostmann.Arithmetic.MovingFieldSpectator
import OAI.NumberTheory.Ostmann.Construction.SpectatorProductNorm

namespace OAI

/-! # Fixed diagrams for the separated modular spectator factors -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The diagram is chosen from the small slots and frequencies before any
bulk values or giant residues are supplied. -/
theorem buildMovingSlotData_field_diagram {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (n : ℕ) (t : FrequencyTree ℤ n)
    (small : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (hfreq : movingGiantFrequencyUnits q n t)
    (hsmall : ((treeLeafProduct n (movingSlotValues value n small) : ℕ) : ZMod q) ≠ 0)
    (hsamples : (samples.values value).UnitsAt q) :
    ∃ (U : (ZMod q)ˣ) (R : RationalTreeData (ZMod q)ˣ n U),
      ∀ (g : ZMod q → ℂ) (D A B : (ZMod q)ˣ)
        (bulk : TreeLeafTuple (List σ) n) (z : TreeLeafTuple (ZMod q)ˣ n),
        TreeNaturalLift n (movingSlotValues value n bulk) z →
        movingModularSpectator value q g D (buildMovingSlotData n t small bulk samples) A B =
          rationalTreeAmplitude g D R A B (transferConjugations n false) z := by
  let T := buildMovingGiantTree n t (movingSlotValues value n small) (samples.values value)
  have hT : T.UnitsAt q := buildMovingGiantTree_units t _ _ hfreq hsmall hsamples
  obtain ⟨U, R, _, _, hR⟩ := T.exists_field_diagram hT
  refine ⟨U, R, ?_⟩
  intro g D A B bulk z hz
  rw [buildMovingSlotData_modular_spectator value g D n t small bulk samples A B z hz]
  exact hR g D A B z false

theorem moving_field_pair_diagrams {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (n : ℕ) (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ side, movingGiantFrequencyUnits q n (t side))
    (hsmall : ∀ side, ((treeLeafProduct n (movingSlotValues value n (small side)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ side, ((samples side).values value).UnitsAt q)
    (D A B : Bool → (ZMod q)ˣ) :
    ∃ d : Bool → SpectatorDiagram q n,
      (∀ side, (d side).conjugations = transferConjugations n false) ∧
      ∀ (g : ZMod q → ℂ) (bulk : Bool → TreeLeafTuple (List σ) n)
        (z : Bool → TreeLeafTuple (ZMod q)ˣ n),
        (∀ side, TreeNaturalLift n (movingSlotValues value n (bulk side)) (z side)) →
        (movingModularSpectator value q g (D false)
          (buildMovingSlotData n (t false) (small false) (bulk false) (samples false)) (A false) (B false) *
          conj (movingModularSpectator value q g (D true)
            (buildMovingSlotData n (t true) (small true) (bulk true) (samples true)) (A true) (B true))) =
          (d false).value g (z false) * conj ((d true).value g (z true)) := by
  have h side := buildMovingSlotData_field_diagram value n (t side) (small side) (samples side)
    (hfreq side) (hsmall side) (hsamples side)
  choose U R hR using h
  let d (side : Bool) : SpectatorDiagram q n :=
    ⟨D side, U side, R side, A side, B side, transferConjugations n false⟩
  refine ⟨d, fun _ => rfl, ?_⟩
  intro g bulk z hz
  rw [hR false g (D false) (A false) (B false) (bulk false) (z false) (hz false),
    hR true g (D true) (A true) (B true) (bulk true) (z true) (hz true)]
  rfl

end Ostmann

end OAI
