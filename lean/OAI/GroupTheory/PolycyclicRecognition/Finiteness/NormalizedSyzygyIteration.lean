import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedSyzygyFunctor

namespace OAI

/-! # Moving one normalized syzygy across an iterated syzygy -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem normalizedSyzygy_iterate_comm (n : ℕ) :
    (normalizedSyzygyFunctor (G := G)) ⋙ iteratedNormalizedSyzygy n =
      iteratedNormalizedSyzygy (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change normalizedSyzygyFunctor ⋙ (iteratedNormalizedSyzygy n ⋙ normalizedSyzygyFunctor) =
      iteratedNormalizedSyzygy (n + 1) ⋙ normalizedSyzygyFunctor
    rw [← Functor.assoc, ih]

def normalizedSyzygyIterationIso (A : Rep.{0} ℤ G) (n : ℕ) :
    (iteratedNormalizedSyzygy n).obj (normalizedSyzygy A) ≅
      (iteratedNormalizedSyzygy (n + 1)).obj A :=
  eqToIso (congrArg (fun F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G => F.obj A)
    (normalizedSyzygy_iterate_comm n))

@[simp]
theorem normalizedSyzygyIterationIso_succ (A : Rep.{0} ℤ G) (n : ℕ) :
    normalizedSyzygyIterationIso A (n + 1) =
      normalizedSyzygyFunctor.mapIso (normalizedSyzygyIterationIso A n) := by
  exact (eqToIso_map normalizedSyzygyFunctor
    (congrArg (fun F : Rep.{0} ℤ G ⥤ Rep.{0} ℤ G => F.obj A)
      (normalizedSyzygy_iterate_comm n))).symm

theorem normalizedSyzygyIterationIso_natural {A B : Rep.{0} ℤ G}
    (f : A ⟶ B) (n : ℕ) :
    (iteratedNormalizedSyzygy n).map (normalizedSyzygyMap f) ≫
        (normalizedSyzygyIterationIso B n).hom =
      (normalizedSyzygyIterationIso A n).hom ≫ (iteratedNormalizedSyzygy (n + 1)).map f := by
  have h := (eqToHom (normalizedSyzygy_iterate_comm (G := G) n)).naturality f
  rw [eqToHom_app, eqToHom_app] at h
  exact h

end PolycyclicRecognition

end

end OAI
