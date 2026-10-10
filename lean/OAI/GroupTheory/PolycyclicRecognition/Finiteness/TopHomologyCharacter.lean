import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyOrientationEquiv
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneCharacter

namespace OAI

/-! # Compatibility of orientation characters under finite-index embeddings -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G K : Type} [Group G] [Group K]

theorem topHomology_character_subgroup (H : Subgroup G) [H.FiniteIndex] (n : ℕ)
    (D : Rep ℤ G) (E : Rep ℤ H)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)))
    (hE : ∀ A : Rep ℤ H, Nonempty (groupHomology A n ≃ₗ[ℤ] (E ⟶ A))) :
    (rankOneCharacter D eD).comp H.subtype = rankOneCharacter E eE := by
  obtain ⟨i⟩ := topHomology_orientation_restrict H n D E eD eE hD hE
  exact rankOneCharacter_eq_of_iso (Rep.res H.subtype D) E eD eE i

theorem topHomology_character_embedding (f : K →* G) (hf : Function.Injective f)
    [f.range.FiniteIndex] (n : ℕ) (D : Rep ℤ G) (E : Rep ℤ K)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)))
    (hE : ∀ A : Rep ℤ K, Nonempty (groupHomology A n ≃ₗ[ℤ] (E ⟶ A))) :
    (rankOneCharacter D eD).comp f = rankOneCharacter E eE := by
  let e := MonoidHom.ofInjective hf
  let F := Rep.res e.symm.toMonoidHom E
  have hF := topHomology_orientation_of_equiv e.symm n E hE
  have hc := topHomology_character_subgroup f.range n D F eD eE hD hF
  ext k
  have he := congrArg (fun c : f.range →* ℤ => c (e k)) hc
  change (rankOneCharacter D eD) (f k) =
    (rankOneCharacter E eE) (e.symm (e k)) at he
  simpa only [e.symm_apply_apply, MonoidHom.comp_apply] using he

end PolycyclicRecognition

end

end OAI
