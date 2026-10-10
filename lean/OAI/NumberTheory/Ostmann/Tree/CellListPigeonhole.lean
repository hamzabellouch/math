import Mathlib.Data.List.OfFn
import Mathlib.Combinatorics.Pigeonhole
import OAI.NumberTheory.Ostmann.Construction.GoodCellSelection

namespace OAI

/-! # Fixing the ordered cell lists across endpoints -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def boundedCellLists (N B : ℕ) : Finset (List ℕ) :=
  (Finset.range (N + 1)).biUnion (fun n =>
    (Finset.univ : Finset (Fin n → Fin (B + 1))).image
      (fun f => List.ofFn (fun i => (f i : ℕ))))

theorem mem_boundedCellLists (N B : ℕ) (w : List ℕ)
    (hlen : w.length ≤ N) (hw : ∀ a ∈ w, a ≤ B) : w ∈ boundedCellLists N B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨w.length, Finset.mem_range.mpr (by omega), ?_⟩
  let f : Fin w.length → Fin (B + 1) := fun i =>
    ⟨w.get i, Nat.lt_succ_of_le (hw _ (List.get_mem _ _))⟩
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, List.ofFn_get w⟩

theorem boundedCellLists_nonempty (N B : ℕ) : (boundedCellLists N B).Nonempty :=
  ⟨[], mem_boundedCellLists N B [] (by simp) (by simp)⟩

theorem boundedCellLists_card_le (N B : ℕ) :
    (boundedCellLists N B).card ≤ (N + 1) * (B + 1) ^ N := by
  calc
    (boundedCellLists N B).card ≤ ∑ n ∈ Finset.range (N + 1),
        ((Finset.univ : Finset (Fin n → Fin (B + 1))).image
          (fun f => List.ofFn (fun i => (f i : ℕ)))).card := Finset.card_biUnion_le
    _ ≤ ∑ n ∈ Finset.range (N + 1), (B + 1) ^ n := by
      apply Finset.sum_le_sum
      intro n _
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n → Fin (B + 1))))
        (f := fun f => List.ofFn (fun i => (f i : ℕ))))
    _ ≤ ∑ _n ∈ Finset.range (N + 1), (B + 1) ^ N := by
      apply Finset.sum_le_sum
      intro n hn
      have : n ≤ N := by have := Finset.mem_range.mp hn; omega
      gcongr
    _ = _ := by simp

/-- Simultaneously fixing all list lengths and ordered cell labels costs
at most the explicit finite number of bounded lists. -/
theorem common_cell_list (E : Finset ℕ) (N B : ℕ) (w : ℕ → List ℕ)
    (hlen : ∀ a ∈ E, (w a).length ≤ N)
    (hentry : ∀ a ∈ E, ∀ h ∈ w a, h ≤ B) :
    ∃ v : List ℕ, ∃ S : Finset ℕ, S ⊆ E ∧
      E.card ≤ ((N + 1) * (B + 1) ^ N) * S.card ∧ ∀ a ∈ S, w a = v := by
  let V := boundedCellLists N B
  have hmap : ∀ a ∈ E, w a ∈ V := fun a ha => mem_boundedCellLists N B (w a) (hlen a ha) (hentry a ha)
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image V
    (fun v => (E.filter (fun a => w a = v)).card) (boundedCellLists_nonempty N B)
  refine ⟨v, E.filter (fun a => w a = v), Finset.filter_subset _ _, ?_, ?_⟩
  · calc
      E.card = ∑ v ∈ V, (E.filter (fun a => w a = v)).card :=
        Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _v ∈ V, (E.filter (fun a => w a = v)).card :=
        Finset.sum_le_sum (fun u hu => hv u hu)
      _ = V.card * (E.filter (fun a => w a = v)).card := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (boundedCellLists_card_le N B)
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end Ostmann

end OAI
