import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantTree
import OAI.NumberTheory.Ostmann.Construction.SpectatorProductNorm

namespace OAI

/-! # Fixed spectator diagrams for the integral moving-giant coefficient

The support multiplier is allowed to include every original arithmetic and
smooth restriction. Only a nonzero multiplier requires integrality. Thus the
identification retains, rather than discards, the original support boundary.
-/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The diagram is chosen before the bulk variables and support multiplier. -/
theorem MovingGiantTree.exists_supported_diagram {q : ℕ} [Fact q.Prime]
    {n C : ℕ} (T : MovingGiantTree n C) (hT : T.UnitsAt q)
    (D : (ZMod q)ˣ) (XL XR : ℕ) (A B : (ZMod q)ˣ)
    (hA : (XL : ZMod q) = A) (hB : (XR : ZMod q) = B) :
    ∃ d : SpectatorDiagram q n,
      d.D = D ∧ d.XL = A ∧ d.XR = B ∧
      d.conjugations = transferConjugations n false ∧
      ∀ (g : ZMod q → ℂ) (x : TreeLeafTuple ℕ n)
        (y : TreeLeafTuple (ZMod q)ˣ n) (c : ℂ),
        TreeNaturalLift n x y → (c ≠ 0 → T.Integral XL XR x) →
        c * movingGiantAmplitude g D T XL XR x = c * d.value g y := by
  obtain ⟨U, R, _, _, he⟩ := T.exists_residue_diagram hT
  refine ⟨⟨D, U, R, A, B, transferConjugations n false⟩,
    rfl, rfl, rfl, rfl, ?_⟩
  intro g x y c hxy hc
  by_cases hc0 : c = 0
  · simp only [hc0, zero_mul]
  · apply congrArg (fun z : ℂ => c * z)
    exact he g D XL XR A B x y hA hB hxy (hc hc0) false

/-- Two original integral histories have the paired factor in (8.5), with
fixed diagrams and a common support multiplier. -/
theorem movingGiant_pair_diagrams {q : ℕ} [Fact q.Prime]
    {n C₁ C₂ : ℕ} (T₁ : MovingGiantTree n C₁) (T₂ : MovingGiantTree n C₂)
    (hT₁ : T₁.UnitsAt q) (hT₂ : T₂.UnitsAt q)
    (D₁ D₂ : (ZMod q)ˣ) (XL₁ XR₁ XL₂ XR₂ : ℕ)
    (A₁ B₁ A₂ B₂ : (ZMod q)ˣ)
    (hA₁ : (XL₁ : ZMod q) = A₁) (hB₁ : (XR₁ : ZMod q) = B₁)
    (hA₂ : (XL₂ : ZMod q) = A₂) (hB₂ : (XR₂ : ZMod q) = B₂) :
    ∃ d₁ d₂ : SpectatorDiagram q n,
      d₁.conjugations = transferConjugations n false ∧
      d₂.conjugations = transferConjugations n false ∧
      ∀ (g : ZMod q → ℂ) (x₁ x₂ : TreeLeafTuple ℕ n)
        (y₁ y₂ : TreeLeafTuple (ZMod q)ˣ n) (c : ℂ),
        TreeNaturalLift n x₁ y₁ → TreeNaturalLift n x₂ y₂ →
        (c ≠ 0 → T₁.Integral XL₁ XR₁ x₁ ∧ T₂.Integral XL₂ XR₂ x₂) →
        c * (movingGiantAmplitude g D₁ T₁ XL₁ XR₁ x₁ *
          conj (movingGiantAmplitude g D₂ T₂ XL₂ XR₂ x₂)) =
        c * (d₁.value g y₁ * conj (d₂.value g y₂)) := by
  obtain ⟨U₁, R₁, _, _, he₁⟩ := T₁.exists_residue_diagram hT₁
  obtain ⟨U₂, R₂, _, _, he₂⟩ := T₂.exists_residue_diagram hT₂
  refine ⟨⟨D₁, U₁, R₁, A₁, B₁, transferConjugations n false⟩,
    ⟨D₂, U₂, R₂, A₂, B₂, transferConjugations n false⟩, rfl, rfl, ?_⟩
  intro g x₁ x₂ y₁ y₂ c hx₁ hx₂ hc
  by_cases hc0 : c = 0
  · simp only [hc0, zero_mul]
  · obtain ⟨hI₁, hI₂⟩ := hc hc0
    have h₁ := he₁ g D₁ XL₁ XR₁ A₁ B₁ x₁ y₁ hA₁ hB₁ hx₁ hI₁ false
    have h₂ := he₂ g D₂ XL₂ XR₂ A₂ B₂ x₂ y₂ hA₂ hB₂ hx₂ hI₂ false
    simpa only [Bool.false_eq_true, ite_false, SpectatorDiagram.value] using
      congrArg₂ (fun z w : ℂ => c * (z * conj w)) h₁ h₂

end Ostmann

end OAI
