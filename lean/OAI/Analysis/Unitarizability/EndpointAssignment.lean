import Mathlib.Combinatorics.Hall.Basic
import OAI.Analysis.Unitarizability.SparseMask

namespace OAI

/-! Infinite endpoint assignment from a finite density inequality.
No countability or distinctness assumption on the edge labels is needed. -/
noncomputable section
namespace Dixmier
open Finset
attribute [local instance] Classical.propDecidable

variable {E V W : Type*}

def endpointSlots (row : E → V) (col : E → W) (r : ℕ)
    (e : E) : Finset ((V × Fin r) ⊕ (W × Fin r)) :=
  (({row e} : Finset V) ×ˢ univ).disjSum (({col e} : Finset W) ×ˢ univ)

/-- All neighboring slots of a finite edge set: endpoints have distinct copies. -/
theorem endpointSlots_biUnion (row : E → V) (col : E → W) (r : ℕ)
    (F : Finset E) :
    F.biUnion (endpointSlots row col r) =
      ((F.image row) ×ˢ (univ : Finset (Fin r))).disjSum ((F.image col) ×ˢ univ) := by
  classical
  ext z
  rcases z with ⟨v, j⟩ | ⟨w, j⟩ <;> simp [endpointSlots]

/-- Infinite Hall matching with r slots at every row and every column. -/
theorem exists_endpoint_assignment (row : E → V) (col : E → W) (r : ℕ)
    (hdensity : ∀ F : Finset E, F.card ≤ r * ((F.image row).card + (F.image col).card)) :
    ∃ f : E → (V × Fin r) ⊕ (W × Fin r), Function.Injective f ∧
      ∀ e, f e ∈ endpointSlots row col r e := by
  classical
  apply (all_card_le_biUnion_card_iff_exists_injective (endpointSlots row col r)).mp
  intro F
  rw [endpointSlots_biUnion]
  simpa only [card_disjSum, card_product, card_univ, Fintype.card_fin, Nat.mul_add,
    Nat.mul_comm] using hdensity F

def slotIndex {r : ℕ} : (V × Fin r) ⊕ (W × Fin r) → Fin r
  | .inl p => p.2
  | .inr p => p.2

def isRowSlot {r : ℕ} : (V × Fin r) ⊕ (W × Fin r) → Bool
  | .inl _ => true
  | .inr _ => false

private theorem assigned_row_eq {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hf : ∀ e, f e ∈ endpointSlots row col r e) (e : E) (h : isRowSlot (f e) = true) :
    f e = Sum.inl (row e, slotIndex (f e)) := by
  have hm := hf e
  cases he : f e with
  | inl p =>
    simp [he, endpointSlots] at hm
    rcases p with ⟨v, j⟩
    simp_all [slotIndex]
  | inr p => simp [he, isRowSlot] at h

private theorem assigned_col_eq {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hf : ∀ e, f e ∈ endpointSlots row col r e) (e : E) (h : isRowSlot (f e) = false) :
    f e = Sum.inr (col e, slotIndex (f e)) := by
  have hm := hf e
  cases he : f e with
  | inl p => simp [he, isRowSlot] at h
  | inr p =>
    simp [he, endpointSlots] at hm
    rcases p with ⟨v, j⟩
    simp_all [slotIndex]

/-- Injectivity of the slot assignment bounds every finite row load. -/
theorem assigned_row_card_le {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hinj : Function.Injective f) (hf : ∀ e, f e ∈ endpointSlots row col r e)
    (v : V) (F : Finset E) (hF : ∀ e ∈ F, row e = v ∧ isRowSlot (f e) = true) :
    F.card ≤ r := by
  classical
  have hi : Set.InjOn (fun e => slotIndex (f e)) (↑F : Set E) := by
    intro e he e' he' hh
    dsimp only at hh
    apply hinj
    rw [assigned_row_eq hf e (hF e he).2, assigned_row_eq hf e' (hF e' he').2]
    rw [(hF e he).1, (hF e' he').1, hh]
  calc
    F.card = (F.image (fun e => slotIndex (f e))).card := (card_image_of_injOn hi).symm
    _ ≤ Fintype.card (Fin r) := card_le_univ _
    _ = r := Fintype.card_fin r

/-- Injectivity also bounds every finite column load. -/
theorem assigned_col_card_le {row : E → V} {col : E → W} {r : ℕ}
    {f : E → (V × Fin r) ⊕ (W × Fin r)}
    (hinj : Function.Injective f) (hf : ∀ e, f e ∈ endpointSlots row col r e)
    (w : W) (F : Finset E) (hF : ∀ e ∈ F, col e = w ∧ isRowSlot (f e) = false) :
    F.card ≤ r := by
  classical
  have hi : Set.InjOn (fun e => slotIndex (f e)) (↑F : Set E) := by
    intro e he e' he' hh
    dsimp only at hh
    apply hinj
    rw [assigned_col_eq hf e (hF e he).2, assigned_col_eq hf e' (hF e' he').2]
    rw [(hF e he).1, (hF e' he').1, hh]
  calc
    F.card = (F.image (fun e => slotIndex (f e))).card := (card_image_of_injOn hi).symm
    _ ≤ Fintype.card (Fin r) := card_le_univ _
    _ = r := Fintype.card_fin r

/-- A sparse mask from finite endpoint density. -/
theorem exists_sparse_mask {G I : Type*} [Group G] [Fintype I] (s : I → G) (r : ℕ)
    (hdensity : ∀ F : Finset (G × I), F.card ≤
      r * ((F.image Prod.fst).card + (F.image (fun e => e.1 * s e.2)).card)) :
    ∃ a : G → I → Bool, (∀ x, (rowOnes a x).card ≤ r) ∧
      ∀ y, (columnZeros a s y).card ≤ r := by
  classical
  obtain ⟨f, hinj, hf⟩ := exists_endpoint_assignment Prod.fst (fun e : G × I => e.1 * s e.2) r hdensity
  let a : G → I → Bool := fun x i => isRowSlot (f (x, i))
  refine ⟨a, ?_, ?_⟩
  · intro x
    let F := (rowOnes a x).image (fun i => (x, i))
    have hF : ∀ e ∈ F, e.1 = x ∧ isRowSlot (f e) = true := by
      rintro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp he
      exact ⟨rfl, (mem_filter.mp hi).2⟩
    have hbound := assigned_row_card_le hinj hf x F hF
    have hi : Function.Injective (fun i : I => (x, i)) := by
      intro i j h
      exact congrArg Prod.snd h
    simpa only [F, card_image_of_injective _ hi] using hbound
  · intro y
    let F := (columnZeros a s y).image (fun i => (y * (s i)⁻¹, i))
    have hF : ∀ e ∈ F, e.1 * s e.2 = y ∧ isRowSlot (f e) = false := by
      rintro e he
      obtain ⟨i, hi, rfl⟩ := mem_image.mp he
      exact ⟨by simp, (mem_filter.mp hi).2⟩
    have hbound := assigned_col_card_le hinj hf y F hF
    have hi : Function.Injective (fun i => (y * (s i)⁻¹, i)) := by
      intro i j h
      exact congrArg Prod.snd h
    simpa only [F, card_image_of_injective _ hi] using hbound

end Dixmier

end

end OAI
