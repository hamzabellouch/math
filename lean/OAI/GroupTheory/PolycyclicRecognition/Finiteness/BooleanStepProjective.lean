import OAI.GroupTheory.PolycyclicRecognition.Algebra.BooleanPartitionMaps
import Mathlib.Data.Set.Countable

namespace OAI

/-! # Countable Boolean step rings are projective over the integers

Enumerating the Boolean coordinates gives a sequence of finite partitions.
Their modules are free, the refinement maps split, and their colimit is the
step ring itself. No freeness theorem about all bounded functions is needed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {X I : Type} (a : I → X → Bool) (b : ℕ → I)

noncomputable def booleanPrefix (n : ℕ) : Finset I := by
  classical
  exact (Finset.range n).image b

theorem booleanPrefix_mono {i j : ℕ} (h : i ≤ j) : booleanPrefix b i ⊆ booleanPrefix b j := by
  classical
  exact Finset.image_subset_image (Finset.range_mono h)

theorem exists_booleanPrefix_contains (hb : Function.Surjective b) (s : Finset I) :
    ∃ n, s ⊆ booleanPrefix b n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert i s _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm⟩ := hb i
    refine ⟨max n (m + 1), Finset.insert_subset_iff.mpr ⟨?_, ?_⟩⟩
    · apply booleanPrefix_mono b (Nat.le_max_right n (m + 1))
      exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), hm⟩
    · exact hn.trans (booleanPrefix_mono b (Nat.le_max_left n (m + 1)))

def booleanPartitionDiagram : SequentialRepresentationDiagram PUnit.{1} where
  obj n := booleanPartitionStage a (booleanPrefix b n)
  map _ _ h := booleanPartitionMap a (booleanPrefix_mono b h)
  map_id n := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    funext c
    rfl
  map_comp i j k hij hjk := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    funext c
    rfl

def booleanStepColimit (hb : Function.Surjective b) :
    (booleanPartitionDiagram a b).ColimitCocone (booleanStepRepresentation a) where
  ι n := booleanPartitionEvaluation a (booleanPrefix b n)
  comm _ _ h := booleanPartitionMap_evaluation a (booleanPrefix_mono b h)
  surj f := by
    obtain ⟨s, hs⟩ := f.property
    obtain ⟨n, hn⟩ := exists_booleanPrefix_contains b hb s
    obtain ⟨v, hv⟩ := dependsOnBoolean_factorization (hs.mono hn)
    refine ⟨n, v, ?_⟩
    apply Subtype.ext
    exact hv.symm
  zero_exact i v hv := by
    refine ⟨i, le_rfl, ?_⟩
    have h0 : v = 0 := booleanPartitionEvaluation_injective a (booleanPrefix b i)
      (hv.trans (map_zero _).symm)
    rw [h0, map_zero]

theorem booleanStepRepresentation_projective (hb : Function.Surjective b) :
    Projective (booleanStepRepresentation a) := by
  let D := booleanPartitionDiagram a b
  let r : ∀ i, D.obj (i + 1) ⟶ D.obj i := fun i =>
    booleanPartitionRetraction a (booleanPrefix_mono b (Nat.le_succ i))
  have hr : ∀ i, D.map i (i + 1) (Nat.le_succ i) ≫ r i = 𝟙 _ :=
    fun i => booleanPartitionMap_retraction a (booleanPrefix_mono b (Nat.le_succ i))
  let : ∀ i, Projective (D.obj i) := fun i => booleanPartitionStage_projective a _
  exact D.split_colimit_projective r hr (booleanStepColimit a b hb)

/-- The small step-function algebra required in the countable group application. -/
theorem booleanStepRing_integer_projective [Countable I] [Nonempty I] :
    Module.Projective ℤ (booleanStepRing a) := by
  obtain ⟨b, hb⟩ := exists_surjective_nat I
  let := booleanStepRepresentation_projective a b hb
  exact integer_projective_of_projective_rep (booleanStepRepresentation a)

end PolycyclicRecognition

end

end OAI
