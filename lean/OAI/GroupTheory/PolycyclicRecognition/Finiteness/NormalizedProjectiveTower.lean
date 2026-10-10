import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectiveTowerComparison

namespace OAI

/-! # Comparison with the normalized complete-cohomology construction -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def normalizedProjectiveTower (A : Rep.{0} ℤ G) : IntegralProjectiveTower G where
  obj n := (iteratedNormalizedSyzygy n).obj A
  projectiveObj n := normalizedFreeRepresentation ((iteratedNormalizedSyzygy n).obj A)
  projective _n := inferInstance
  ι n := kernel.ι (normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A))
  π n := normalizedFreeAugmentation ((iteratedNormalizedSyzygy n).obj A)
  zero _n := kernel.condition _
  shortExact _n := normalizedSyzygySequence_shortExact _

def normalizedProjectiveTowerCohomology (A : Rep.{0} ℤ G) (p : ℕ) :
    (normalizedProjectiveTower A).Cohomology p ≃ₗ[ℤ] ShiftedCompletedCohomology p A :=
  LinearEquiv.refl ℤ _

def IntegralProjectiveTower.completeCohomologyEquiv (T : IntegralProjectiveTower G)
    (A : Rep.{0} ℤ G) (e : T.obj 0 ≅ A) (p : ℕ) :
    T.Cohomology p ≃ₗ[ℤ] ShiftedCompletedCohomology p A :=
  (IntegralProjectiveTower.cohomologyEquiv (show T.obj 0 ≅ (normalizedProjectiveTower A).obj 0 from e) p).trans
    (normalizedProjectiveTowerCohomology A p)

def normalizedProjectiveTowerMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    IntegralProjectiveTower.Map (normalizedProjectiveTower A) (normalizedProjectiveTower B) where
  app n := (iteratedNormalizedSyzygy n).map f
  cover n := normalizedFreeMap ((iteratedNormalizedSyzygy n).map f)
  comm_left _n := normalizedSyzygyMap_ι _
  comm_right _n := normalizedFreeAugmentation_natural _

theorem normalizedProjectiveTowerMap_cohomology {A B : Rep.{0} ℤ G} (f : A ⟶ B) (p : ℕ)
    (x : (normalizedProjectiveTower A).Cohomology p) :
    normalizedProjectiveTowerCohomology B p ((normalizedProjectiveTowerMap f).cohomologyMap p x) =
      shiftedCompletedCohomologyMap p f (normalizedProjectiveTowerCohomology A p x) := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  rw [IntegralProjectiveTower.Map.cohomologyMap_of]
  change shiftedCohomologyStage p A n at z
  change Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p B) n
      (shiftedCohomologyStageMap p f n z) =
    shiftedCompletedCohomologyMap p f
      (Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p A) n z)
  rw [shiftedCompletedCohomologyMap_of]

def IntegralProjectiveTower.normalization (T : IntegralProjectiveTower G) :
    IntegralProjectiveTower.Map T (normalizedProjectiveTower (T.obj 0)) :=
  IntegralProjectiveTower.liftMap T (normalizedProjectiveTower (T.obj 0)) (𝟙 _)

theorem IntegralProjectiveTower.completeCohomologyEquiv_apply
    (T : IntegralProjectiveTower G) (p : ℕ) (x : T.Cohomology p) :
    T.completeCohomologyEquiv (T.obj 0) (Iso.refl _) p x =
      normalizedProjectiveTowerCohomology (T.obj 0) p (T.normalization.cohomologyMap p x) := rfl

theorem IntegralProjectiveTower.completeCohomologyEquiv_natural
    {T U : IntegralProjectiveTower G} (f : IntegralProjectiveTower.Map T U)
    (p : ℕ) (x : T.Cohomology p) :
    U.completeCohomologyEquiv (U.obj 0) (Iso.refl _) p (f.cohomologyMap p x) =
      shiftedCompletedCohomologyMap p (f.app 0)
        (T.completeCohomologyEquiv (T.obj 0) (Iso.refl _) p x) := by
  rw [IntegralProjectiveTower.completeCohomologyEquiv_apply,
    IntegralProjectiveTower.completeCohomologyEquiv_apply,
    ← normalizedProjectiveTowerMap_cohomology]
  have h : (f.comp U.normalization).cohomologyMap p =
      (T.normalization.comp (normalizedProjectiveTowerMap (f.app 0))).cohomologyMap p := by
    apply IntegralProjectiveTower.Map.cohomologyMap_eq_of_stable_eq
    change stableRepresentationClass _ _ (f.app 0 ≫ 𝟙 _) =
      stableRepresentationClass _ _ (𝟙 _ ≫ f.app 0)
    rw [Category.comp_id, Category.id_comp]
  have he := LinearMap.congr_fun h x
  rw [IntegralProjectiveTower.Map.cohomologyMap_comp,
    IntegralProjectiveTower.Map.cohomologyMap_comp] at he
  exact congrArg (normalizedProjectiveTowerCohomology (U.obj 0) p) he

end PolycyclicRecognition

end

end OAI
