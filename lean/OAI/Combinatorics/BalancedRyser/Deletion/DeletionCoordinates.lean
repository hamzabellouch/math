import Mathlib
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

namespace Balanced.DeletionCoordinates

open Finset

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

def assemble (D : I → Finset A) : Finset (I × A) :=
  univ.filter (fun l => l.2 ∈ D l.1)

def fiber (S : Finset (I × A)) (i : I) : Finset A :=
  univ.filter (fun a => (i, a) ∈ S)

omit [DecidableEq I] in
@[simp] theorem mem_assemble (D : I → Finset A) (l : I × A) :
    l ∈ assemble D ↔ l.2 ∈ D l.1 := by simp [assemble]

omit [Fintype I] in
@[simp] theorem mem_fiber (S : Finset (I × A)) (i : I) (a : A) :
    a ∈ fiber S i ↔ (i, a) ∈ S := by simp [fiber]

@[simp] theorem fiber_assemble (D : I → Finset A) : fiber (assemble D) = D := by
  funext i
  ext a
  simp

@[simp] theorem assemble_fiber (S : Finset (I × A)) : assemble (fiber S) = S := by
  ext l
  simp

def arrayEquiv : (I → Finset A) ≃ Finset (I × A) where
  toFun := assemble
  invFun := fiber
  left_inv := fiber_assemble
  right_inv := assemble_fiber

omit [Fintype I] in
theorem filter_direction_eq_image (S : Finset (I × A)) (i : I) :
    S.filter (fun l => l.1 = i) = (fiber S i).image (fun a => (i, a)) := by
  ext ⟨j, a⟩
  simp only [mem_filter, mem_image, mem_fiber, Prod.mk.injEq]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨a, h, rfl, rfl⟩
  · rintro ⟨b, hb, rfl, rfl⟩
    exact ⟨hb, rfl⟩

omit [Fintype I] in
theorem card_filter_direction (S : Finset (I × A)) (i : I) :
    (S.filter (fun l => l.1 = i)).card = (fiber S i).card := by
  rw [filter_direction_eq_image]
  exact card_image_of_injective _ (fun a b h => congrArg Prod.snd h)

@[simp] theorem card_assemble_direction (D : I → Finset A) (i : I) :
    ((assemble D).filter (fun l => l.1 = i)).card = (D i).card := by
  rw [card_filter_direction, fiber_assemble]

def fixedSizeEquiv (k : ℕ) :
    {D : I → Finset A // ∀ i, (D i).card = k} ≃
      {S : Finset (I × A) // ∀ i, (S.filter (fun l => l.1 = i)).card = k} :=
  arrayEquiv.subtypeEquiv (fun D => by simp [arrayEquiv])

theorem card_directionalSubsets (k : ℕ) :
    Fintype.card {S : Finset (I × A) //
      ∀ i, (S.filter (fun l => l.1 = i)).card = k} =
      (Nat.choose (Fintype.card A) k) ^ Fintype.card I := by
  rw [← Fintype.card_congr (fixedSizeEquiv (I := I) (A := A) k)]
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi
    (β := fun _ : I => Finset A) (p := fun _ D => D.card = k))]
  simp

section Relabel

variable {J B : Type*} [Fintype J] [Fintype B] [DecidableEq J] [DecidableEq B]

def relabelArray (eI : I ≃ J) (eA : A ≃ B) :
    (I → Finset A) ≃ (J → Finset B) :=
  Equiv.arrowCongr eI eA.finsetCongr

omit [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
  [Fintype J] [Fintype B] [DecidableEq J] [DecidableEq B] in
@[simp] theorem relabelArray_apply (eI : I ≃ J) (eA : A ≃ B)
    (D : I → Finset A) (j : J) :
    relabelArray eI eA D j = (D (eI.symm j)).map eA.toEmbedding := rfl

def fixedSizeRelabelEquiv (eI : I ≃ J) (eA : A ≃ B) (k : ℕ) :
    {D : I → Finset A // ∀ i, (D i).card = k} ≃
      {D : J → Finset B // ∀ j, (D j).card = k} :=
  (relabelArray eI eA).subtypeEquiv (fun D => by
    simp only [relabelArray_apply, card_map]
    exact eI.symm.surjective.forall)

def coordinateLineEquiv (eI : I ≃ J) (eA : A ≃ B) (k : ℕ) :
    {D : I → Finset A // ∀ i, (D i).card = k} ≃
      {S : Finset (J × B) // ∀ j, (S.filter (fun l => l.1 = j)).card = k} :=
  (fixedSizeRelabelEquiv eI eA k).trans (fixedSizeEquiv k)

end Relabel
end Balanced.DeletionCoordinates

namespace Balanced.DeletionCoordinates

noncomputable def affineCoordinateLineEquiv (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] (k : ℕ) :
    {D : Fin (Fintype.card F + 1) → Finset (Fin (Fintype.card F)) //
      ∀ i, (D i).card = k} ≃
    {S : Finset (Line F) // ∀ d : Direction F,
      (S.filter (fun l => l.1 = d)).card = k} :=
  coordinateLineEquiv
    (Fintype.equivFinOfCardEq (α := Direction F) (by simp [Direction])).symm
    (Fintype.equivFin F).symm k

theorem card_affineDeletionSets (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] (k : ℕ) :
    Fintype.card {S : Finset (Line F) // ∀ d : Direction F,
      (S.filter (fun l => l.1 = d)).card = k} =
      (Nat.choose (Fintype.card F) k) ^ (Fintype.card F + 1) := by
  simpa only [Direction, Fintype.card_option] using
    card_directionalSubsets (I := Direction F) (A := F) k

end Balanced.DeletionCoordinates

end OAI
