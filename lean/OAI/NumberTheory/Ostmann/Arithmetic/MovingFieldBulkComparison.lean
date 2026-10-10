import OAI.NumberTheory.Ostmann.Arithmetic.MovingFieldDiagram
import OAI.NumberTheory.Ostmann.Construction.NormalizedSpectatorComparison

namespace OAI

/-! # Good-matching decay for the separated field spectator diagrams -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem moving_field_good_spectator_comparison {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (value : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (t : Bool → FrequencyTree ℤ (n + 2))
    (small : Bool → TreeLeafTuple (List σ) (n + 2))
    (samples : Bool → MovingSampleSlots σ (n + 2))
    (hfreq : ∀ side, movingGiantFrequencyUnits q (n + 2) (t side))
    (hsmall : ∀ side,
      ((treeLeafProduct (n + 2) (movingSlotValues value (n + 2) (small side)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ side, ((samples side).values value).UnitsAt q)
    (D A B : Bool → (ZMod q)ˣ)
    (S : Finset (ZMod q)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSq : S.card < q)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (q : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) :
    ∃ d : Bool → SpectatorDiagram q (n + 2),
      (∀ (bulk : Bool → TreeLeafTuple (List σ) (n + 2))
        (z : Bool → TreeLeafTuple (ZMod q)ˣ (n + 2)),
        (∀ side, TreeNaturalLift (n + 2) (movingSlotValues value (n + 2) (bulk side)) (z side)) →
        (movingModularSpectator value q (normalizedResidueTransform S) (D false)
          (buildMovingSlotData (n + 2) (t false) (small false) (bulk false) (samples false))
          (A false) (B false) *
          conj (movingModularSpectator value q (normalizedResidueTransform S) (D true)
            (buildMovingSlotData (n + 2) (t true) (small true) (bulk true) (samples true))
            (A true) (B true))) =
          (d false).value (normalizedResidueTransform S) (z false) *
            conj ((d true).value (normalizedResidueTransform S) (z true))) ∧
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ,
          (d false).bulkValue (normalizedResidueTransform S) x *
            conj ((d true).bulkValue (normalizedResidueTransform S) (x ∘ e.symm)))‖ ^ 2 ≤
        quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (q : ℝ))) := by
  obtain ⟨d, hconj, hd⟩ := moving_field_pair_diagrams value (n + 2) t small samples
    hfreq hsmall hsamples D A B
  refine ⟨d, hd (normalizedResidueTransform S), ?_⟩
  let c := treeLeafTupleEquiv Bool n (transferConjugations n false)
  apply normalized_spectator_bulk_comparison hq n m hm e hgood S hlo hhi hS hSq
    β ε hε hε1 hprincipal hβ hbias (d false) (d true) c (fun j => !(c j))
  intro j
  rw [hconj false]
  simpa only [Bool.not_not] using transferConjugations_quartet n false j

end Ostmann

end OAI
