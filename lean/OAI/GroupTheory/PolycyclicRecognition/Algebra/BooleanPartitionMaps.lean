import OAI.GroupTheory.PolycyclicRecognition.Algebra.BooleanStepRing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubsingletonGroupProjective

namespace OAI

/-! # Evaluation and split refinement maps for finite Boolean partitions -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {X I : Type} (a : I → X → Bool)

/-- Forget some of the Boolean coordinates of a realized partition cell. -/
def booleanPartitionRefine {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionCell a t → booleanPartitionCell a s := fun c =>
  ⟨fun i => c.val ⟨i.val, h i.property⟩, by
    obtain ⟨x, hx⟩ := c.property
    refine ⟨x, ?_⟩
    funext i
    exact congrFun hx ⟨i.val, h i.property⟩⟩

@[simp]
theorem booleanPartitionRefine_point {s t : Finset I} (h : s ⊆ t) (x : X) :
    booleanPartitionRefine a h (booleanPartitionPoint a t x) = booleanPartitionPoint a s x := rfl

theorem booleanPartitionRefine_surjective {s t : Finset I} (h : s ⊆ t) :
    Function.Surjective (booleanPartitionRefine a h) := by
  intro c
  exact ⟨booleanPartitionPoint a t (booleanPartitionRepresentative a s c),
    booleanPartitionPoint_representative a s c⟩

abbrev booleanPartitionStage (s : Finset I) : Rep ℤ PUnit.{1} :=
  Rep.trivial ℤ PUnit.{1} (booleanPartitionCell a s → ℤ)

instance booleanPartitionStage_projective (s : Finset I) :
    Projective (booleanPartitionStage a s) := by
  let := Fintype.ofFinite (booleanPartitionCell a s)
  apply projective_rep_of_integer_projective

/-- Pull a step function back to a finer partition. -/
def booleanPartitionMap {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionStage a s ⟶ booleanPartitionStage a t :=
  subsingletonGroupRepHom {
    toFun v c := v (booleanPartitionRefine a h c)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/-- Choose one refined cell above each old cell to obtain a retraction. -/
def booleanPartitionRetraction {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionStage a t ⟶ booleanPartitionStage a s :=
  subsingletonGroupRepHom {
    toFun v c := v (Function.surjInv (booleanPartitionRefine_surjective a h) c)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

theorem booleanPartitionMap_retraction {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionMap a h ≫ booleanPartitionRetraction a h = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  funext c
  exact congrArg v (Function.surjInv_eq (booleanPartitionRefine_surjective a h) c)

abbrev booleanStepRepresentation : Rep ℤ PUnit.{1} := Rep.trivial ℤ PUnit.{1} (booleanStepRing a)

def booleanPartitionEvaluation (s : Finset I) :
    booleanPartitionStage a s ⟶ booleanStepRepresentation a :=
  subsingletonGroupRepHom {
    toFun v := ⟨fun x => v (booleanPartitionPoint a s x), s, by
      intro x y hxy
      apply congrArg v
      apply Subtype.ext
      funext i
      exact hxy i i.property⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

theorem booleanPartitionEvaluation_injective (s : Finset I) :
    Function.Injective (booleanPartitionEvaluation a s).hom := by
  intro v w h
  funext c
  have hc := congrArg (fun f : booleanStepRing a => f.val
    (booleanPartitionRepresentative a s c)) h
  change v (booleanPartitionPoint a s (booleanPartitionRepresentative a s c)) =
    w (booleanPartitionPoint a s (booleanPartitionRepresentative a s c)) at hc
  simpa only [booleanPartitionPoint_representative] using hc

theorem booleanPartitionMap_evaluation {s t : Finset I} (h : s ⊆ t) :
    booleanPartitionMap a h ≫ booleanPartitionEvaluation a t =
      booleanPartitionEvaluation a s := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext x
  rfl

end PolycyclicRecognition

end

end OAI
