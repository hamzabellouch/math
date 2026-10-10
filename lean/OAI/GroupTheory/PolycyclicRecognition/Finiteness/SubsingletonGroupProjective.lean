import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SplitProjectiveColimit
import Mathlib.Algebra.Category.ModuleCat.Projective

namespace OAI

/-! # Projectivity for the trivial group and underlying integer modules -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Subsingleton G]

def subsingletonGroupRepHom {A B : Rep.{0} ℤ G} (f : A →ₗ[ℤ] B) : A ⟶ B :=
  Rep.ofHom ⟨f, fun g => by
    have hg : g = 1 := Subsingleton.elim _ _
    subst g
    simp only [map_one, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]⟩

theorem projective_rep_of_integer_projective (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] : Projective A where
  factors {E X} f p := by
    intro hp
    obtain ⟨l, hl⟩ := Module.projective_lifting_property p.hom.toLinearMap f.hom.toLinearMap
      ((Rep.epi_iff_surjective p).mp hp)
    refine ⟨subsingletonGroupRepHom l, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact hl

theorem integer_projective_of_projective_rep (A : Rep.{0} ℤ G)
    [Projective A] : Module.Projective ℤ A := by
  apply Module.Projective.of_lifting_property''
  intro f hf
  let F : Rep ℤ G := Rep.trivial ℤ G (A →₀ ℤ)
  let p : F ⟶ A := subsingletonGroupRepHom f
  let : Epi p := (Rep.epi_iff_surjective p).mpr hf
  let l := Projective.factorThru (𝟙 A) p
  refine ⟨l.hom.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom (Projective.factorThru_comp (𝟙 A) p) x

end PolycyclicRecognition

end

end OAI
