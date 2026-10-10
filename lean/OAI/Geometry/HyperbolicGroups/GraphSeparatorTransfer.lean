import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [DecidableEq W]

lemma preconnected_image (G : SimpleGraph V) (H : SimpleGraph W) (f : G →g H)
    (U : Finset V) (hc : (G.induce (U : Set V)).Preconnected) :
    (H.induce (U.image f : Set W)).Preconnected := by
  let g : G.induce (U : Set V) →g H.induce (U.image f : Set W) := {
    toFun := fun v => ⟨f v,Finset.mem_image.mpr ⟨v,v.property,rfl⟩⟩
    map_rel' := fun h => f.map_adj h }
  apply hc.map g
  intro w
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp w.property
  exact ⟨⟨v,hv⟩,Subtype.ext he⟩

/-- Stability of the actual component-separator conclusion under an
injective graph homomorphism; separator vertices outside the given carrier
are not charged. -/
theorem component_separator_pullback (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) (hinj : Function.Injective f) (c : ℕ)
    (hH : ∀ U : Finset W, ∃ S : Finset W, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
      ∀ A : Finset W, A ⊆ U → Disjoint A S →
        (H.induce (A : Set W)).Preconnected → 2*A.card ≤ U.card)
    (U : Finset V) :
    ∃ S : Finset V, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
      ∀ A : Finset V, A ⊆ U → Disjoint A S →
        (G.induce (A : Set V)).Preconnected → 2*A.card ≤ U.card := by
  classical
  obtain ⟨S,hSU,hSc,hsep⟩ := hH (U.image f)
  let S' := U.filter (fun v => f v ∈ S)
  have he : S'.image f = S := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2
    · intro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (hSU hw)
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,hw⟩,rfl⟩
  have hcS : S'.card = S.card := (Finset.card_image_of_injective S' hinj).symm.trans (congrArg Finset.card he)
  have hcU := Finset.card_image_of_injective U hinj
  refine ⟨S',Finset.filter_subset _ _,?_,?_⟩
  · rw [hcS]
    simpa only [hcU] using hSc
  · intro A hAU hAS hconn
    have hh := hsep (A.image f) (Finset.image_mono f hAU) (by
      apply Finset.disjoint_left.mpr
      intro w hw hwS
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact Finset.disjoint_left.mp hAS hv (Finset.mem_filter.mpr ⟨hAU hv,hwS⟩))
      (preconnected_image G H f A hconn)
    simpa only [Finset.card_image_of_injective _ hinj] using hh

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
