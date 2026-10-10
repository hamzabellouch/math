import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationDiagram

namespace OAI

/-! # Degree-zero complete cohomology from normalized syzygies

The transition maps are the actual connecting homomorphisms of the natural
short exact free-cover sequences. No vanishing theorem is assumed here.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

abbrev normalizedCohomologyStage (A : Rep.{0} ℤ G) (n : ℕ) : Type :=
  groupCohomology ((iteratedNormalizedSyzygy n).obj A) n

def normalizedCohomologyStageMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    normalizedCohomologyStage A n →ₗ[ℤ] normalizedCohomologyStage B n :=
  (groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy n).map f) n).hom

@[simp]
theorem normalizedCohomologyStageMap_id (A : Rep.{0} ℤ G) (n : ℕ) :
    normalizedCohomologyStageMap (𝟙 A) n = LinearMap.id := by
  unfold normalizedCohomologyStageMap
  rw [CategoryTheory.Functor.map_id, groupCohomology.map_id]
  rfl

theorem normalizedCohomologyStageMap_comp {A B C : Rep.{0} ℤ G}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    normalizedCohomologyStageMap (f ≫ g) n =
      (normalizedCohomologyStageMap g n).comp (normalizedCohomologyStageMap f n) := by
  unfold normalizedCohomologyStageMap
  rw [CategoryTheory.Functor.map_comp, groupCohomology.map_id_comp]
  rfl

theorem normalizedSyzygyConnecting_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B) (n : ℕ) :
    normalizedSyzygyConnecting A n ≫
        groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy (n + 1)).map f) (n + 1) =
      groupCohomology.map (MonoidHom.id G) ((iteratedNormalizedSyzygy n).map f) n ≫
        normalizedSyzygyConnecting B n :=
  groupCohomology.δ_naturality
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj A))
    (normalizedSyzygySequence_shortExact ((iteratedNormalizedSyzygy n).obj B))
    (normalizedSyzygySequenceMap ((iteratedNormalizedSyzygy n).map f)) n (n + 1) rfl

def normalizedCohomologyForward (A : Rep.{0} ℤ G) (i j : ℕ) (h : i ≤ j) :
    normalizedCohomologyStage A i →ₗ[ℤ] normalizedCohomologyStage A j where
  toFun := Nat.leRecOn h (fun {k} => (normalizedSyzygyConnecting A k).hom)
  map_add' x y := by
    induction h with
    | refl => simp only [Nat.leRecOn_self]
    | @step j h ih => simp only [Nat.leRecOn_succ h, map_add, ih]
  map_smul' r x := by
    induction h with
    | refl => simp only [Nat.leRecOn_self, RingHom.id_apply]
    | @step j h ih =>
      simp only [Nat.leRecOn_succ h, ih, RingHom.id_apply]
      exact (normalizedSyzygyConnecting A j).hom.map_smul r _

instance normalizedCohomologyForward_directed (A : Rep.{0} ℤ G) :
    DirectedSystem (normalizedCohomologyStage A)
      (fun i j h => normalizedCohomologyForward A i j h) where
  map_self := by intro i x; exact Nat.leRecOn_self x
  map_map := by intro k j i hij hjk x; exact (Nat.leRecOn_trans hij hjk x).symm

theorem normalizedCohomologyForward_natural {A B : Rep.{0} ℤ G} (f : A ⟶ B)
    (i j : ℕ) (h : i ≤ j) (x : normalizedCohomologyStage A i) :
    normalizedCohomologyStageMap f j (normalizedCohomologyForward A i j h x) =
      normalizedCohomologyForward B i j h (normalizedCohomologyStageMap f i x) := by
  induction h with
  | refl =>
    simp only [normalizedCohomologyForward, Nat.leRecOn_self]
    rfl
  | @step j h ih =>
    change normalizedCohomologyStageMap f (j + 1)
      (Nat.leRecOn (C := normalizedCohomologyStage A) _
        (fun {k} => (normalizedSyzygyConnecting A k).hom) x) =
      Nat.leRecOn (C := normalizedCohomologyStage B) _
        (fun {k} => (normalizedSyzygyConnecting B k).hom) _
    rw [Nat.leRecOn_succ h, Nat.leRecOn_succ h]
    have hn := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (normalizedSyzygyConnecting_natural f j)) (normalizedCohomologyForward A i j h x)
    change normalizedCohomologyStageMap f (j + 1)
      ((normalizedSyzygyConnecting A j).hom _) =
        (normalizedSyzygyConnecting B j).hom
          (normalizedCohomologyForward B i j h (normalizedCohomologyStageMap f i x))
    rw [← ih]
    exact hn

abbrev CompletedCohomology (A : Rep.{0} ℤ G) :=
  Module.DirectLimit (normalizedCohomologyStage A) (normalizedCohomologyForward A)

def completedCohomologyMap {A B : Rep.{0} ℤ G} (f : A ⟶ B) :
    CompletedCohomology A →ₗ[ℤ] CompletedCohomology B :=
  Module.DirectLimit.map (f := normalizedCohomologyForward A)
    (f' := normalizedCohomologyForward B) (normalizedCohomologyStageMap f)
    (fun i j h => by
      apply LinearMap.ext
      exact normalizedCohomologyForward_natural f i j h)

@[simp]
theorem completedCohomologyMap_of {A B : Rep.{0} ℤ G} (f : A ⟶ B) (i : ℕ)
    (x : normalizedCohomologyStage A i) :
    completedCohomologyMap f
      (Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward A) i x) =
    Module.DirectLimit.of ℤ ℕ _ (normalizedCohomologyForward B) i
      (normalizedCohomologyStageMap f i x) := by
  exact Module.DirectLimit.map_apply_of (normalizedCohomologyStageMap f)
    (fun i j h => by
      apply LinearMap.ext
      exact normalizedCohomologyForward_natural f i j h) x

def completedCohomologyFunctor : Rep.{0} ℤ G ⥤ ModuleCat ℤ where
  obj A := ModuleCat.of ℤ (CompletedCohomology A)
  map f := ModuleCat.ofHom (completedCohomologyMap f)
  map_id A := by
    apply ModuleCat.hom_ext
    change completedCohomologyMap (𝟙 A) = LinearMap.id
    apply DFunLike.ext
    intro x
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
    rw [completedCohomologyMap_of]
    rw [normalizedCohomologyStageMap_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    change completedCohomologyMap (f ≫ g) =
      (completedCohomologyMap g).comp (completedCohomologyMap f)
    apply DFunLike.ext
    intro x
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of x
    simp only [LinearMap.comp_apply, completedCohomologyMap_of]
    rw [normalizedCohomologyStageMap_comp]
    rfl

end PolycyclicRecognition

end

end OAI
