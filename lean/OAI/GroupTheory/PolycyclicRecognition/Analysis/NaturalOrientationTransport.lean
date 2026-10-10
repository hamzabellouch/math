import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TopHomologyNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneRepresentation

namespace OAI

/-! # Naturality for a prescribed top-homology orientation -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem topHomology_orientation_unique (n : ℕ) (D E : Rep ℤ G)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)))
    (hE : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (E ⟶ A))) :
    Nonempty (D ≅ E) := by
  obtain ⟨d⟩ := hD E
  obtain ⟨e⟩ := hE E
  let b := d.symm.trans e
  have hid : (𝟙 E : E ⟶ E) ≠ 0 := by
    intro h
    have hv := congrArg (fun f : E ⟶ E => eE (f.hom (eE.symm 1))) h
    simp at hv
  have hf : b.symm (𝟙 E) ≠ 0 := by
    intro h
    apply hid
    have he := congrArg b h
    simpa using he
  exact rankOne_rep_iso_of_nonzero D E eD eE (b.symm (𝟙 E)) hf

theorem topHomology_natural_prescribed {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (D : Rep ℤ G)
    (eD : D.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A))) :
    ∃ e : ∀ A : Rep ℤ G, groupHomology A n ≃ₗ[ℤ] (D ⟶ A),
      ∀ (A B : Rep ℤ G) (f : A ⟶ B) (x : groupHomology A n),
        e B (groupHomology.map (MonoidHom.id G) f n x) = e A x ≫ f := by
  obtain ⟨E, ⟨eE⟩, e, he⟩ := hG.topHomology_natural
  obtain ⟨j⟩ := topHomology_orientation_unique n D E eD eE hD (fun A => ⟨e A⟩)
  refine ⟨fun A => (e A).trans (Linear.homCongr ℤ j.symm (Iso.refl A)), ?_⟩
  intro A B f x
  change (j.hom ≫ e B (groupHomology.map (MonoidHom.id G) f n x)) ≫ 𝟙 B =
    ((j.hom ≫ e A x) ≫ 𝟙 A) ≫ f
  rw [he, Category.comp_id, Category.comp_id, Category.assoc]

end PolycyclicRecognition

end

end OAI
