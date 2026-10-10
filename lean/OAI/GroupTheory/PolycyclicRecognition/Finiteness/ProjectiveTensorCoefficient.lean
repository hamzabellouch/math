import OAI.GroupTheory.PolycyclicRecognition.Algebra.SmallCoefficientConstants

namespace OAI

/-! # Tensoring projectives by an integer-projective coefficient

The internal Hom is exact on epimorphisms when its first argument is
projective over the integers. The tensor–Hom adjunction then preserves
projective representations, with no finite-rank assumption.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem representation_ihom_preserves_epimorphisms (A : Rep.{0} ℤ G)
    [Module.Projective ℤ A] : (ihom A).PreservesEpimorphisms where
  preserves {X Y} f hf := by
    apply (Rep.epi_iff_surjective _).mpr
    intro u
    change A →ₗ[ℤ] Y at u
    obtain ⟨v, hv⟩ := Module.projective_lifting_property f.hom.toLinearMap u
      ((Rep.epi_iff_surjective f).mp hf)
    exact ⟨v, hv⟩

theorem representation_tensor_projective (A P : Rep.{0} ℤ G)
    [Module.Projective ℤ A] [Projective P] : Projective (A ⊗ P) := by
  let := representation_ihom_preserves_epimorphisms A
  let := Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ihom.adjunction A)
  exact Functor.projective_obj (tensorLeft A) P

end PolycyclicRecognition

end

end OAI
