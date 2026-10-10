import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledCochains
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! # Controlled support under face maps

Deleting a vertex has finite fibers once the pairwise differences of the
original tuple are bounded. This supplies the local finiteness needed by
the homogeneous cochain differential.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type*} [Group G] {n : ℕ}

/-- Faces of a controlled tuple retain the same scale. -/
theorem IsControlledTuple.face {S : Set G} {x : Fin (n + 2) → G}
    (hx : IsControlledTuple S x) (i : Fin (n + 2)) :
    IsControlledTuple S (x ∘ i.succAbove) :=
  fun j k => hx (i.succAbove j) (i.succAbove k)

/-- On controlled tuples a fixed face has only finitely many possible
missing vertices. -/
theorem finite_controlled_face_fiber (S : Set G) (hS : S.Finite)
    (i : Fin (n + 2)) (y : Fin (n + 1) → G) :
    {x : Fin (n + 2) → G | IsControlledTuple S x ∧ x ∘ i.succAbove = y}.Finite := by
  let A : Set G := Set.range y ∪ (fun s => y 0 * s) '' S
  have hA : A.Finite := (Set.finite_range y).union (hS.image _)
  apply (Set.Finite.pi' (fun _ : Fin (n + 2) => hA)).subset
  intro x hx k
  rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, hk⟩
  · rw [hk]
    apply Or.inr
    refine ⟨(y 0)⁻¹ * x i, ?_, by simp⟩
    have hy : x (i.succAbove 0) = y 0 := congrFun hx.2 0
    rw [← hy]
    exact hx.1 _ _
  · rw [hk]
    apply Or.inl
    exact ⟨j, (congrFun hx.2 j).symm⟩

variable {R : Type*} [CommRing R]

/-- Face pullback preserves locally finite support. -/
def controlledFace (i : Fin (n + 2)) :
    controlledCochains R G n →ₗ[R] controlledCochains R G (n + 1) where
  toFun c := ⟨fun x => c (x ∘ i.succAbove), by
    intro S hS
    let C := {y : Fin (n + 1) → G | IsControlledTuple S y ∧ c y ≠ 0}
    have hC : C.Finite := c.property S hS
    have hF : (⋃ y ∈ C,
        {x : Fin (n + 2) → G | IsControlledTuple S x ∧ x ∘ i.succAbove = y}).Finite :=
      hC.biUnion (fun y _ => finite_controlled_face_fiber S hS i y)
    apply hF.subset
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x ∘ i.succAbove,
      Set.mem_iUnion.mpr ⟨⟨hx.1.face i, hx.2⟩, hx.1, rfl⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem controlledFace_apply (i : Fin (n + 2))
    (c : controlledCochains R G n) (x : Fin (n + 2) → G) :
    controlledFace i c x = c (x ∘ i.succAbove) := rfl

/-- The homogeneous coboundary, as an actual map on controlled cochains. -/
def controlledCoboundary :
    controlledCochains R G n →ₗ[R] controlledCochains R G (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : R) ^ i.val • controlledFace i

@[simp] theorem controlledCoboundary_apply (c : controlledCochains R G n)
    (x : Fin (n + 2) → G) :
    controlledCoboundary c x = ∑ i : Fin (n + 2), (-1 : R) ^ i.val * c (x ∘ i.succAbove) := by
  simp [controlledCoboundary, smul_eq_mul]

/-- Coordinatewise coarse pullback commutes with the homogeneous coboundary. -/
theorem controlledCoboundary_pullback {H : Type*} [Group H]
    (e : GroupCoarseEquivalence G H) (c : controlledCochains R H n) :
    controlledCoboundary (controlledCochainPullback e n c) =
      controlledCochainPullback e (n + 1) (controlledCoboundary c) := by
  apply Subtype.ext
  funext x
  simp only [controlledCoboundary_apply, controlledCochainPullback_apply]
  rfl

end PolycyclicRecognition

end

end OAI
