import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomology

namespace OAI

/-! # Nonnegative degree shifts of complete cohomology

The hierarchy argument uses positive connecting degrees. The n-th stage is
H^(n+p)(G, Omega^n A), with the actual coefficient connecting maps.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

def shiftedSyzygyConnecting (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) :
    groupCohomology ((iteratedNormalizedSyzygy n).obj A) (n + p) ⟶
      groupCohomology ((iteratedNormalizedSyzygy (n + 1)).obj A) (n + 1 + p) :=
  groupCohomology.δ (normalizedSyzygySequence_shortExact
    ((iteratedNormalizedSyzygy n).obj A)) (n + p) (n + 1 + p) (by omega)

abbrev shiftedCohomologyStage (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) : Type :=
  groupCohomology ((iteratedNormalizedSyzygy n).obj A) (n + p)

def shiftedCohomologyStageMap (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    shiftedCohomologyStage p A n →ₗ[ℤ] shiftedCohomologyStage p B n :=
  (groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy n).map f) (n + p)).hom

@[simp]
theorem shiftedCohomologyStageMap_id (p : ℕ) (A : Rep.{0} ℤ G) (n : ℕ) :
    shiftedCohomologyStageMap p (𝟙 A) n = LinearMap.id := by
  unfold shiftedCohomologyStageMap
  rw [CategoryTheory.Functor.map_id, groupCohomology.map_id]
  rfl

theorem shiftedCohomologyStageMap_comp (p : ℕ) {A B C : Rep.{0} ℤ G}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    shiftedCohomologyStageMap p (f ≫ g) n =
      (shiftedCohomologyStageMap p g n).comp (shiftedCohomologyStageMap p f n) := by
  unfold shiftedCohomologyStageMap
  rw [CategoryTheory.Functor.map_comp, groupCohomology.map_id_comp]
  rfl

theorem shiftedSyzygyConnecting_natural (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    shiftedSyzygyConnecting p A n ≫
        groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy (n + 1)).map f) (n + 1 + p) =
      groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy n).map f) (n + p) ≫
        shiftedSyzygyConnecting p B n :=
  groupCohomology.δ_naturality
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A))
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj B))
    (normalizedSyzygySequenceMap ((iteratedNormalizedSyzygy n).map f)) (n + p) (n + 1 + p) (by omega)

def shiftedCohomologyForward (p : ℕ) (A : Rep.{0} ℤ G) (i j : ℕ) (h : i ≤ j) :
    shiftedCohomologyStage p A i →ₗ[ℤ] shiftedCohomologyStage p A j where
  toFun := Nat.leRecOn h (fun {k} => (shiftedSyzygyConnecting p A k).hom)
  map_add' x y := by
    induction h with
    | refl => simp only [Nat.leRecOn_self]
    | @step j h ih => simp only [Nat.leRecOn_succ h, map_add, ih]
  map_smul' r x := by
    induction h with
    | refl => simp only [Nat.leRecOn_self, RingHom.id_apply]
    | @step j h ih =>
      simp only [Nat.leRecOn_succ h, ih, RingHom.id_apply]
      exact (shiftedSyzygyConnecting p A j).hom.map_smul r _

instance shiftedCohomologyForward_directed (p : ℕ) (A : Rep.{0} ℤ G) :
    DirectedSystem (shiftedCohomologyStage p A)
      (fun i j h => shiftedCohomologyForward p A i j h) where
  map_self := by intro i x; exact Nat.leRecOn_self x
  map_map := by intro k j i hij hjk x; exact (Nat.leRecOn_trans hij hjk x).symm

theorem shiftedCohomologyForward_natural (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (i j : ℕ) (h : i ≤ j) (x : shiftedCohomologyStage p A i) :
    shiftedCohomologyStageMap p f j (shiftedCohomologyForward p A i j h x) =
      shiftedCohomologyForward p B i j h (shiftedCohomologyStageMap p f i x) := by
  induction h with
  | refl =>
    simp only [shiftedCohomologyForward, Nat.leRecOn_self]
    rfl
  | @step j h ih =>
    change shiftedCohomologyStageMap p f (j + 1)
      (Nat.leRecOn (C := shiftedCohomologyStage p A) _
        (fun {k} => (shiftedSyzygyConnecting p A k).hom) x) =
      Nat.leRecOn (C := shiftedCohomologyStage p B) _
        (fun {k} => (shiftedSyzygyConnecting p B k).hom) _
    rw [Nat.leRecOn_succ h, Nat.leRecOn_succ h]
    have hn := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (shiftedSyzygyConnecting_natural p f j)) (shiftedCohomologyForward p A i j h x)
    change shiftedCohomologyStageMap p f (j + 1)
      ((shiftedSyzygyConnecting p A j).hom _) =
        (shiftedSyzygyConnecting p B j).hom
          (shiftedCohomologyForward p B i j h (shiftedCohomologyStageMap p f i x))
    rw [← ih]
    exact hn

abbrev ShiftedCompletedCohomology (p : ℕ) (A : Rep.{0} ℤ G) :=
  Module.DirectLimit (shiftedCohomologyStage p A) (shiftedCohomologyForward p A)

def shiftedCompletedCohomologyMap (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    ShiftedCompletedCohomology p A →ₗ[ℤ] ShiftedCompletedCohomology p B :=
  Module.DirectLimit.map (f := shiftedCohomologyForward p A)
    (f' := shiftedCohomologyForward p B) (shiftedCohomologyStageMap p f)
    (fun i j h => by
      apply LinearMap.ext
      exact shiftedCohomologyForward_natural p f i j h)

@[simp]
theorem shiftedCompletedCohomologyMap_of (p : ℕ) {A B : Rep.{0} ℤ G} (f : A ⟶ B) (i : ℕ)
    (x : shiftedCohomologyStage p A i) :
    shiftedCompletedCohomologyMap p f
      (Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p A) i x) =
    Module.DirectLimit.of ℤ ℕ _ (shiftedCohomologyForward p B) i
      (shiftedCohomologyStageMap p f i x) := by
  exact Module.DirectLimit.map_apply_of (shiftedCohomologyStageMap p f)
    (fun i j h => by
      apply LinearMap.ext
      exact shiftedCohomologyForward_natural p f i j h) x

def shiftedCompletedCohomologyFunctor (p : ℕ) : Rep.{0} ℤ G ⥤ ModuleCat ℤ where
  obj A := ModuleCat.of ℤ (ShiftedCompletedCohomology p A)
  map f := ModuleCat.ofHom (shiftedCompletedCohomologyMap p f)
  map_id A := by
    apply ModuleCat.hom_ext
    change shiftedCompletedCohomologyMap p (𝟙 A) = LinearMap.id
    apply DFunLike.ext
    intro x
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
    rw [shiftedCompletedCohomologyMap_of]
    rw [shiftedCohomologyStageMap_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    change shiftedCompletedCohomologyMap p (f ≫ g) =
      (shiftedCompletedCohomologyMap p g).comp (shiftedCompletedCohomologyMap p f)
    apply DFunLike.ext
    intro x
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
    simp only [LinearMap.comp_apply, shiftedCompletedCohomologyMap_of]
    rw [shiftedCohomologyStageMap_comp]
    rfl

end PolycyclicRecognition

end

end OAI
