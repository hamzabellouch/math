import OAI.GroupTheory.PolycyclicRecognition.Finiteness.UnitaryReducedVanishing

namespace OAI

/-! # Descent of compact coboundary approximations along a group quotient

Compact lifts suffice. Injectivity and compactness of the kernel are not
needed, which is essential for the overlapping Cartan factor map.
-/

noncomputable section
namespace PolycyclicRecognition

universe u v w

variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

theorem UnitaryReducedVanishing.of_surjective_compact_lifts
    (hH : UnitaryReducedVanishing.{v, w} H) (f : H →* G) (hf : Continuous f)
    (hsurj : Function.Surjective f)
    (hlift : ∀ Q : Set G, IsCompact Q → ∃ K : Set H, IsCompact K ∧ Q ⊆ f '' K) :
    UnitaryReducedVanishing.{u, w} G := by
  intro E _ _ _ ρ hfix hρ b hbc hb Q hQ ε hε
  obtain ⟨K, hK, hQK⟩ := hlift Q hQ
  have hfixH : ∀ v, (∀ h : H, ρ (f h) v = v) → v = 0 := by
    intro v hv
    apply hfix v
    intro g
    obtain ⟨h, rfl⟩ := hsurj g
    exact hv h
  have hbH : IsUnitaryCocycle (ρ.comp f) (b ∘ f) := by
    intro g h
    change b (f (g * h)) = _
    rw [map_mul]
    exact hb _ _
  obtain ⟨φ, hφ⟩ := hH E (ρ.comp f) hfixH (fun v => (hρ v).comp hf)
    (b ∘ f) (hbc.comp hf) hbH K hK ε hε
  refine ⟨φ, fun q hq => ?_⟩
  obtain ⟨h, hh, rfl⟩ := hQK hq
  exact hφ h hh

end PolycyclicRecognition

end

end OAI
