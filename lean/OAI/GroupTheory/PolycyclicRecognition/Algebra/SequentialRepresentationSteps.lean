import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationDiagram

namespace OAI

/-! # Sequential diagrams specified by their consecutive arrows -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (A : ℕ → Rep.{0} ℤ G) (f : ∀ n, A n ⟶ A (n + 1))

def consecutiveMap (i j : ℕ) (h : i ≤ j) : A i ⟶ A j :=
  Nat.leRecOn h (fun {k} a => a ≫ f k) (𝟙 (A i))

@[simp]
theorem consecutiveMap_self (i : ℕ) : consecutiveMap A f i i le_rfl = 𝟙 (A i) :=
  Nat.leRecOn_self _

@[simp]
theorem consecutiveMap_step (i j : ℕ) (h : i ≤ j) :
    consecutiveMap A f i (j + 1) (Nat.le_succ_of_le h) =
      consecutiveMap A f i j h ≫ f j := by
  unfold consecutiveMap
  exact Nat.leRecOn_succ (C := fun k => A i ⟶ A k) h
    (next := fun {k} a => a ≫ f k) (𝟙 (A i))

theorem consecutiveMap_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    consecutiveMap A f i j hij ≫ consecutiveMap A f j k hjk =
      consecutiveMap A f i k (hij.trans hjk) := by
  induction hjk with
  | refl => simp
  | @step k h ih =>
    rw [consecutiveMap_step A f j k h,
      consecutiveMap_step A f i k (hij.trans h), ← Category.assoc, ih]

def ofConsecutive : SequentialRepresentationDiagram G where
  obj := A
  map := consecutiveMap A f
  map_id := consecutiveMap_self A f
  map_comp := consecutiveMap_comp A f

@[simp]
theorem ofConsecutive_map_step (i : ℕ) :
    (ofConsecutive A f).map i (i + 1) (Nat.le_succ i) = f i := by
  change consecutiveMap A f i (i + 1) (Nat.le_succ i) = f i
  rw [consecutiveMap_step A f i i le_rfl, consecutiveMap_self, Category.id_comp]

theorem ofConsecutive_comm (B : Rep.{0} ℤ G) (u : ∀ i, A i ⟶ B)
    (hu : ∀ i, f i ≫ u (i + 1) = u i) (i j : ℕ) (h : i ≤ j) :
    (ofConsecutive A f).map i j h ≫ u j = u i := by
  induction h with
  | refl =>
    change consecutiveMap A f i i le_rfl ≫ u i = u i
    rw [consecutiveMap_self, Category.id_comp]
  | @step j h ih =>
    change consecutiveMap A f i (j + 1) _ ≫ u (j + 1) = u i
    rw [consecutiveMap_step, Category.assoc, hu]
    exact ih

end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
