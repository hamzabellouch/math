import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ShiftedCohomologyDimensionShift
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ProjectivePresentationComparison

namespace OAI

/-! # Stable maps and projective presentations in complete cohomology -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem shiftedCompleteFunctor_map_zero_of_stable_zero
    (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (hf : stableRepresentationClass A B f = 0) :
    (shiftedCompletedCohomologyFunctor p).map f = 0 := by
  obtain ⟨P, hP, u, v, huv⟩ :=
    (stableRepresentationClass_eq_zero_iff_projective_factor f).mp hf
  let : Projective P := hP
  let : Subsingleton (ShiftedCompletedCohomology p P) :=
    shiftedCompleteCohomology_subsingleton_of_finite_projectiveDimension p P 0
  have hu : (shiftedCompletedCohomologyFunctor p).map u = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change shiftedCompletedCohomologyMap p u x = 0
    exact Subsingleton.elim _ _
  rw [← huv, Functor.map_comp, hu, zero_comp]

theorem shiftedCompleteFunctor_map_eq_of_stable_eq
    (p : ℕ) {A B : Rep.{0} ℤ G} (f g : A ⟶ B)
    (hfg : stableRepresentationClass A B f = stableRepresentationClass A B g) :
    (shiftedCompletedCohomologyFunctor p).map f =
      (shiftedCompletedCohomologyFunctor p).map g := by
  have hz : stableRepresentationClass A B (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have h := shiftedCompleteFunctor_map_zero_of_stable_zero p (f - g) hz
  rw [Functor.map_sub] at h
  exact sub_eq_zero.mp h

theorem shiftedCompleteMap_eq_of_stable_eq
    (p : ℕ) {A B : Rep.{0} ℤ G} (f g : A ⟶ B)
    (hfg : stableRepresentationClass A B f = stableRepresentationClass A B g) :
    shiftedCompletedCohomologyMap p f = shiftedCompletedCohomologyMap p g :=
  congrArg ModuleCat.Hom.hom (shiftedCompleteFunctor_map_eq_of_stable_eq p f g hfg)

theorem shiftedCompleteMap_zero_of_stable_zero
    (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (hf : stableRepresentationClass A B f = 0) :
    shiftedCompletedCohomologyMap p f = 0 :=
  congrArg ModuleCat.Hom.hom (shiftedCompleteFunctor_map_zero_of_stable_zero p f hf)

theorem shiftedCompletedCohomologyMap_comp_apply (p : ℕ) {A B C : Rep.{0} ℤ G}
    (f : A ⟶ B) (g : B ⟶ C) (x : ShiftedCompletedCohomology p A) :
    shiftedCompletedCohomologyMap p (f ≫ g) x =
      shiftedCompletedCohomologyMap p g (shiftedCompletedCohomologyMap p f x) :=
  ConcreteCategory.congr_hom ((shiftedCompletedCohomologyFunctor p).map_comp f g) x

def shiftedCompleteStableIso (p : ℕ) {A B : Rep.{0} ℤ G}
    (a : A ⟶ B) (b : B ⟶ A)
    (hab : stableRepresentationClass A A (a ≫ b) = stableRepresentationClass A A (𝟙 A))
    (hba : stableRepresentationClass B B (b ≫ a) = stableRepresentationClass B B (𝟙 B)) :
    (shiftedCompletedCohomologyFunctor p).obj A ≅
      (shiftedCompletedCohomologyFunctor p).obj B where
  hom := (shiftedCompletedCohomologyFunctor p).map a
  inv := (shiftedCompletedCohomologyFunctor p).map b
  hom_inv_id := by
    rw [← Functor.map_comp, shiftedCompleteFunctor_map_eq_of_stable_eq p _ _ hab,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← Functor.map_comp, shiftedCompleteFunctor_map_eq_of_stable_eq p _ _ hba,
      CategoryTheory.Functor.map_id]

theorem projectivePresentation_completeEquiv
    (p : ℕ) (S : ShortComplex (Rep.{0} ℤ G)) (hS : S.ShortExact) [Projective S.X₂] :
    Nonempty (ShiftedCompletedCohomology (p + 1) S.X₁ ≃ₗ[ℤ]
      ShiftedCompletedCohomology p S.X₃) := by
  obtain ⟨a, b, hab, hba⟩ := projectivePresentation_stable_comparison S hS
  exact ⟨((shiftedCompleteStableIso (p + 1) a b hab hba).toLinearEquiv.symm.toAddEquiv.trans
    (shiftedSyzygyAddEquiv p S.X₃)).toIntLinearEquiv⟩

end PolycyclicRecognition

end

end OAI
