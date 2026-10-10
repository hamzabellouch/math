import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ShiftedCompleteCohomologyAdditive
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalizedSyzygyIteration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialModuleTail

namespace OAI

/-! # Dimension shifting in the completed coefficient theory -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Module.DirectLimit.module
variable {G : Type} [Group G]

def shiftedSyzygyStageIso (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) :
    groupCohomology ((iteratedNormalizedSyzygy n).obj (normalizedSyzygy A)) (n + (p + 1)) ≅
      groupCohomology ((iteratedNormalizedSyzygy (n + 1)).obj A) (n + 1 + p) :=
  (groupCohomology.functor ℤ G (n + (p + 1))).mapIso (normalizedSyzygyIterationIso A n) ≪≫
    eqToIso (congrArg (fun d => groupCohomology ((iteratedNormalizedSyzygy (n + 1)).obj A) d)
      (show n + (p + 1) = n + 1 + p by omega))

theorem cohomologyConnecting_reindex (S : ShortComplex (Rep.{0} ℤ G))
    (hS : S.ShortExact) (i j k l : ℕ) (hij : i + 1 = j) (hkl : k + 1 = l)
    (hik : i = k) (hjl : j = l) :
    groupCohomology.δ hS i j hij ≫
        (eqToIso (congrArg (fun d => groupCohomology S.X₁ d) hjl)).hom =
      (eqToIso (congrArg (fun d => groupCohomology S.X₃ d) hik)).hom ≫
        groupCohomology.δ hS k l hkl := by
  subst k
  subst l
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem shiftedSyzygyStageIso_connecting (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) :
    shiftedSyzygyConnecting (p + 1) (normalizedSyzygy A) n ≫
        (shiftedSyzygyStageIso p A (n + 1)).hom =
      (shiftedSyzygyStageIso p A n).hom ≫ shiftedSyzygyConnecting p A (n + 1) := by
  let e := normalizedSyzygyIterationIso A n
  let Y := (iteratedNormalizedSyzygy (n + 1)).obj A
  have hn := groupCohomology.δ_naturality
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj (normalizedSyzygy A)))
    (normalizedSyzygySequence_shortExact Y)
    (normalizedSyzygySequenceMap e.hom)
    (n + (p + 1)) (n + 1 + (p + 1)) (by omega)
  change shiftedSyzygyConnecting (p + 1) (normalizedSyzygy A) n ≫
      (groupCohomology.functor ℤ G (n + 1 + (p + 1))).map
        (normalizedSyzygyFunctor.map e.hom) =
    (groupCohomology.functor ℤ G (n + (p + 1))).map e.hom ≫
      groupCohomology.δ (normalizedSyzygySequence_shortExact Y)
        (n + (p + 1)) (n + 1 + (p + 1)) (by omega) at hn
  have ht := cohomologyConnecting_reindex (normalizedSyzygySequence Y)
    (normalizedSyzygySequence_shortExact Y)
    (n + (p + 1)) (n + 1 + (p + 1)) (n + 1 + p) (n + 1 + 1 + p)
    (by omega) (by omega) (by omega) (by omega)
  simp only [shiftedSyzygyStageIso, normalizedSyzygyIterationIso_succ]
  change shiftedSyzygyConnecting (p + 1) (normalizedSyzygy A) n ≫
      ((groupCohomology.functor ℤ G (n + 1 + (p + 1))).map
        (normalizedSyzygyFunctor.map e.hom) ≫ _) = _
  erw [← Category.assoc, hn, Category.assoc, ht, ← Category.assoc]


theorem shiftedCohomologyForward_succ (p : ℕ) (A : Rep.{0} ℤ G)
    (i j : ℕ) (h : i ≤ j) (x : shiftedCohomologyStage p A i) :
    shiftedCohomologyForward p A i (j + 1) (Nat.le_succ_of_le h) x =
      (shiftedSyzygyConnecting p A j).hom (shiftedCohomologyForward p A i j h x) := by
  exact Nat.leRecOn_succ (C := shiftedCohomologyStage p A) h x

theorem shiftedSyzygyStageIso_forward (p : ℕ) (A : Rep.{0} ℤ G)
    (i j : ℕ) (h : i ≤ j)
    (x : shiftedCohomologyStage (p + 1) (normalizedSyzygy A) i) :
    (shiftedSyzygyStageIso p A j).hom
        (shiftedCohomologyForward (p + 1) (normalizedSyzygy A) i j h x) =
      shiftedCohomologyForward p A (i + 1) (j + 1) (Nat.add_le_add_right h 1)
        ((shiftedSyzygyStageIso p A i).hom x) := by
  induction h with
  | refl =>
    simp only [shiftedCohomologyForward, Nat.leRecOn_self]
    rfl
  | @step j h ih =>
    rw [shiftedCohomologyForward_succ (p + 1) (normalizedSyzygy A) i j h,
      shiftedCohomologyForward_succ p A (i + 1) (j + 1) (Nat.add_le_add_right h 1)]
    have he := ConcreteCategory.congr_hom (shiftedSyzygyStageIso_connecting p A j)
      (shiftedCohomologyForward (p + 1) (normalizedSyzygy A) i j h x)
    change (shiftedSyzygyStageIso p A (j + 1)).hom
      ((shiftedSyzygyConnecting (p + 1) (normalizedSyzygy A) j).hom _) =
        (shiftedSyzygyConnecting p A (j + 1)).hom
          ((shiftedSyzygyStageIso p A j).hom _) at he
    rw [he, ih]

def shiftedSyzygyTailEquiv (p : ℕ) (A : Rep.{0} ℤ G) :
    ShiftedCompletedCohomology (p + 1) (normalizedSyzygy A) ≃ₗ[ℤ]
      ModuleTailLimit (shiftedCohomologyStage p A) (shiftedCohomologyForward p A) :=
  Module.DirectLimit.congr (f := shiftedCohomologyForward (p + 1) (normalizedSyzygy A))
    (f' := moduleTailMap (shiftedCohomologyStage p A) (shiftedCohomologyForward p A))
    (fun n => (shiftedSyzygyStageIso p A n).toLinearEquiv) (by
      intro i j h
      apply LinearMap.ext
      exact shiftedSyzygyStageIso_forward p A i j h)

def shiftedSyzygyEquiv (p : ℕ) (A : Rep.{0} ℤ G) :
    ShiftedCompletedCohomology (p + 1) (normalizedSyzygy A) ≃ₗ[ℤ]
      ShiftedCompletedCohomology p A :=
  (shiftedSyzygyTailEquiv p A).trans
    (sequentialModuleTailEquiv (shiftedCohomologyStage p A) (shiftedCohomologyForward p A))

def shiftedSyzygyAddEquiv (p : ℕ) (A : Rep.{0} ℤ G) :
    ShiftedCompletedCohomology (p + 1) (normalizedSyzygy A) ≃+
      ShiftedCompletedCohomology p A :=
  (shiftedSyzygyEquiv p A).toAddEquiv

theorem cohomologyMap_reindex {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (i j : ℕ) (h : i = j) :
    (groupCohomology.functor ℤ G i).map f ≫
        (eqToIso (congrArg (fun d => groupCohomology B d) h)).hom =
      (eqToIso (congrArg (fun d => groupCohomology A d) h)).hom ≫
        (groupCohomology.functor ℤ G j).map f := by
  subst j
  change (groupCohomology.functor ℤ G i).map f ≫ 𝟙 _ =
    𝟙 _ ≫ (groupCohomology.functor ℤ G i).map f
  rw [Category.comp_id, Category.id_comp]

theorem shiftedSyzygyStageIso_natural (p : ℕ) {A B : Rep.{0} ℤ G}
    (f : A ⟶ B) (n : ℕ) :
    (groupCohomology.functor ℤ G (n + (p + 1))).map
        ((iteratedNormalizedSyzygy n).map (normalizedSyzygyMap f)) ≫
        (shiftedSyzygyStageIso p B n).hom =
      (shiftedSyzygyStageIso p A n).hom ≫
        (groupCohomology.functor ℤ G (n + 1 + p)).map
          ((iteratedNormalizedSyzygy (n + 1)).map f) := by
  have h := congrArg ((groupCohomology.functor ℤ G (n + (p + 1))).map)
    (normalizedSyzygyIterationIso_natural f n)
  simp only [CategoryTheory.Functor.map_comp] at h
  simp only [shiftedSyzygyStageIso]
  erw [← Category.assoc, h, Category.assoc,
    cohomologyMap_reindex _ (n + (p + 1)) (n + 1 + p) (by omega), ← Category.assoc]

theorem shiftedSyzygyEquiv_of (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ)
    (x : shiftedCohomologyStage (p + 1) (normalizedSyzygy A) n) :
    shiftedSyzygyAddEquiv p A
        (Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward (p + 1) (normalizedSyzygy A)) n x) =
      Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p A) (n + 1)
        ((shiftedSyzygyStageIso p A n).hom x) := by
  change moduleTailToOriginal (shiftedCohomologyStage p A) (shiftedCohomologyForward p A)
    (shiftedSyzygyTailEquiv p A
      (Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward (p + 1) (normalizedSyzygy A)) n x)) = _
  unfold shiftedSyzygyTailEquiv
  rw [Module.DirectLimit.congr_apply_of, moduleTailToOriginal_of]
  rfl

theorem shiftedSyzygyEquiv_natural (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (x : ShiftedCompletedCohomology (p + 1) (normalizedSyzygy A)) :
    shiftedSyzygyAddEquiv p B (shiftedCompletedCohomologyMap (p + 1) (normalizedSyzygyMap f) x) =
      shiftedCompletedCohomologyMap p f (shiftedSyzygyAddEquiv p A x) := by
  obtain ⟨n, z, rfl⟩ := Module.DirectLimit.exists_of x
  rw [shiftedCompletedCohomologyMap_of, shiftedSyzygyEquiv_of,
    shiftedSyzygyEquiv_of, shiftedCompletedCohomologyMap_of]
  congr 1
  exact ConcreteCategory.congr_hom (shiftedSyzygyStageIso_natural p f n) z

theorem shiftedSyzygyEquiv_symm_natural (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (x : ShiftedCompletedCohomology p A) :
    (shiftedSyzygyAddEquiv p B).symm (shiftedCompletedCohomologyMap p f x) =
      shiftedCompletedCohomologyMap (p + 1) (normalizedSyzygyMap f)
        ((shiftedSyzygyAddEquiv p A).symm x) := by
  apply (shiftedSyzygyAddEquiv p B).injective
  rw [AddEquiv.apply_symm_apply, shiftedSyzygyEquiv_natural, AddEquiv.apply_symm_apply]

end PolycyclicRecognition

end

end OAI
