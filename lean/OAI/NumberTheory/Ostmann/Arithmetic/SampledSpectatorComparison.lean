import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantSamples
import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantSpectator
import OAI.NumberTheory.Ostmann.Construction.NormalizedSpectatorComparison

namespace OAI

/-! # The good-matching bound for the constructed compensation histories -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The actual sampled small data produce fixed diagrams, the exact supported
integer coefficient, and the good-matching decay for their uniform residues. -/
theorem sampled_good_spectator_comparison {q : ℕ} [Fact q.Prime] (hq : 3 ≤ q)
    (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (t₁ t₂ : FrequencyTree ℤ (n + 2))
    (small₁ small₂ : TreeLeafTuple ℕ (n + 2))
    (samples₁ samples₂ : MovingGiantSamples (n + 2))
    (hfreq₁ : movingGiantFrequencyUnits q (n + 2) t₁)
    (hfreq₂ : movingGiantFrequencyUnits q (n + 2) t₂)
    (hsmall₁ : ((treeLeafProduct (n + 2) small₁ : ℕ) : ZMod q) ≠ 0)
    (hsmall₂ : ((treeLeafProduct (n + 2) small₂ : ℕ) : ZMod q) ≠ 0)
    (hsamples₁ : samples₁.UnitsAt q) (hsamples₂ : samples₂.UnitsAt q)
    (D₁ D₂ : (ZMod q)ˣ) (XL₁ XR₁ XL₂ XR₂ : ℕ)
    (A₁ B₁ A₂ B₂ : (ZMod q)ˣ)
    (hA₁ : (XL₁ : ZMod q) = A₁) (hB₁ : (XR₁ : ZMod q) = B₁)
    (hA₂ : (XL₂ : ZMod q) = A₂) (hB₂ : (XR₂ : ZMod q) = B₂)
    (S : Finset (ZMod q)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSq : S.card < q)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (q : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) :
    let T₁ := buildMovingGiantTree (n + 2) t₁ small₁ samples₁
    let T₂ := buildMovingGiantTree (n + 2) t₂ small₂ samples₂
    ∃ d₁ d₂ : SpectatorDiagram q (n + 2),
      (∀ (x₁ x₂ : TreeLeafTuple ℕ (n + 2))
        (y₁ y₂ : TreeLeafTuple (ZMod q)ˣ (n + 2)) (c : ℂ),
        TreeNaturalLift (n + 2) x₁ y₁ → TreeNaturalLift (n + 2) x₂ y₂ →
        (c ≠ 0 → T₁.Integral XL₁ XR₁ x₁ ∧ T₂.Integral XL₂ XR₂ x₂) →
        c * (movingGiantAmplitude (normalizedResidueTransform S) D₁ T₁ XL₁ XR₁ x₁ *
          conj (movingGiantAmplitude (normalizedResidueTransform S) D₂ T₂ XL₂ XR₂ x₂)) =
        c * (d₁.value (normalizedResidueTransform S) y₁ *
          conj (d₂.value (normalizedResidueTransform S) y₂))) ∧
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ,
          d₁.bulkValue (normalizedResidueTransform S) x *
            conj (d₂.bulkValue (normalizedResidueTransform S) (x ∘ e.symm)))‖ ^ 2 ≤
        quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (q : ℝ))) := by
  dsimp only
  obtain ⟨d₁, d₂, hc₁, _, hvalue⟩ := movingGiant_pair_diagrams
    (buildMovingGiantTree (n + 2) t₁ small₁ samples₁)
    (buildMovingGiantTree (n + 2) t₂ small₂ samples₂)
    (buildMovingGiantTree_units t₁ small₁ samples₁ hfreq₁ hsmall₁ hsamples₁)
    (buildMovingGiantTree_units t₂ small₂ samples₂ hfreq₂ hsmall₂ hsamples₂)
    D₁ D₂ XL₁ XR₁ XL₂ XR₂ A₁ B₁ A₂ B₂ hA₁ hB₁ hA₂ hB₂
  refine ⟨d₁, d₂, hvalue (normalizedResidueTransform S), ?_⟩
  let c := treeLeafTupleEquiv Bool n (transferConjugations n false)
  apply normalized_spectator_bulk_comparison hq n m hm e hgood S hlo hhi hS hSq β ε
    hε hε1 hprincipal hβ hbias d₁ d₂ c (fun j => !(c j))
  intro j
  rw [hc₁]
  simpa only [Bool.not_not] using transferConjugations_quartet n false j

end Ostmann

end OAI
