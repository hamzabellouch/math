import OAI.NumberTheory.Ostmann.Construction.SelectedBulkPermutation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalMatchedCorrelation
import OAI.NumberTheory.Ostmann.Characters.MixedExternalAverage

namespace OAI

/-! # The original coefficient and common transform under bulk reassignment -/

namespace Ostmann
open scoped Classical BigOperators

theorem MovingSlotReversal.naturalProduct_selected_bulk {B A : Type*}
    (value : A → ℕ) (n m : ℕ) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → A)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    naturalProduct (value ∘ selectedBulkSample slot e y)
      (flattenMovingSlots n small ++ flattenMovingSlots n (bulkSlotLeaves n m slot)) =
    naturalProduct (value ∘ y)
      (flattenMovingSlots n small ++ flattenMovingSlots n (bulkSlotLeaves n m slot)) := by
  have hs : (flattenMovingSlots n small).map (selectedBulkSample slot e y) =
      (flattenMovingSlots n small).map y :=
    List.map_congr_left (fun i hi => selectedBulkSample_nonbulk slot e y i (hsmall i hi))
  have hb : (flattenMovingSlots n (bulkSlotLeaves n m slot)).map (selectedBulkSample slot e y) =
      (flattenMovingSlots n (bulkSlotLeaves n m (slot ∘ e.symm))).map y := by
    rw [← flattenMovingSlots_map, selectedBulkSample_bulk_leaves, flattenMovingSlots_map]
  unfold naturalProduct
  simp only [← List.map_map, List.map_append, List.prod_append]
  rw [hs, hb]
  exact congrArg (_ * ·) (((bulkSlotLeaves_perm_matching n m slot e).map y).map value).prod_eq

theorem movingExternalDiagonalWeight_selectedBulkSample {B A : Type*}
    (value : A → ℕ) (outside : List ℕ) (n m : ℕ)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → A)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ)
    (Jleft Jright : ℝ) (diagonal : Bool) (x z : ℝ) :
    movingExternalDiagonalWeight value outside small (bulkSlotLeaves n m slot)
      greg s φ Jleft Jright diagonal (selectedBulkSample slot e y) x z =
    movingExternalDiagonalWeight value outside small (bulkSlotLeaves n m slot)
      greg s φ Jleft Jright diagonal y x z := by
  unfold movingExternalDiagonalWeight
  rw [MovingSlotReversal.naturalProduct_selected_bulk value n m small slot e y hsmall]

theorem movingExternalDiagonalWeight_positive {B A : Type*} {n : ℕ}
    (value : A → ℕ) (outside : List ℕ) (small bulk : TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Jleft Jright : ℝ) (diagonal : Bool) (y : B → A) (x z : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧
      movingExternalDiagonalWeight value outside small bulk greg s φ Jleft Jright diagonal y x z = t := by
  have hc (a : ℝ) (J : ℝ) : 0 ≤ positiveLogCutoff φ J a := by
    unfold positiveLogCutoff
    split_ifs
    · exact hφ _
    · exact le_rfl
  unfold movingExternalDiagonalWeight giantOuterWeight
  let a := positiveLogCutoff φ Jleft (⌊Real.exp x⌋₊ : ℝ)
  let b := positiveLogCutoff φ Jright (⌊Real.exp z⌋₊ : ℝ)
  let c := if diagonal then Real.exp Jright / (⌊Real.exp z⌋₊ : ℝ) else 1
  refine ⟨a * b * c * ‖primeProductTransform greg
    (outside.prod * ⌊Real.exp x⌋₊ * ⌊Real.exp z⌋₊)
    (MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk)) s‖ ^ 2, ?_, ?_⟩
  · have ha : 0 ≤ a := hc _ _
    have hb : 0 ≤ b := hc _ _
    have hc' : 0 ≤ c := by dsimp [c]; split_ifs <;> positivity
    positivity
  · dsimp only [a, b, c]
    cases diagonal <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> push_cast <;> rfl

theorem movingFrequencyCoefficient_bulk_action {σ B : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n m : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (e : Equiv.Perm (TreeLeafIndex n × Fin m)) (y : B → σ) (XL XR : ℕ)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (treeLeafMap (List.map (selectedBulkSample slot e y)) n small)
      (treeLeafMap (List.map (selectedBulkSample slot e y)) n (bulkSlotLeaves n m slot)) XL XR =
    movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (treeLeafMap (List.map y) n small)
      (treeLeafMap (List.map y) n (bulkSlotLeaves n m (slot ∘ e.symm))) XL XR := by
  rw [selectedBulkSample_small_leaves n small slot e y hsmall,
    selectedBulkSample_bulk_leaves]

theorem movingOriginalMatchedCorrelation_bulk_action {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) :
    let F := fun s y x z => movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s
      (treeLeafMap (List.map y) n small)
      (treeLeafMap (List.map y) n (bulkSlotLeaves n m slot)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    movingOriginalMatchedCorrelation q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n small (movingPatternBulkLeaves n m slot e) greg
      Jleft Jright diagonal u v r w center =
    mixedExternalAverage ν (V n) u v r w center (fun s y x z =>
      (F s y x z * star (F s (selectedBulkSample slot e y) x z)) *
        movingExternalDiagonalWeight value outside small (bulkSlotLeaves n m slot)
          greg s φ Jleft Jright diagonal y x z) := by
  dsimp only
  simp only [mixedExternalAverage, movingOriginalMatchedCorrelation,
    movingPatternBulkLeaves, Bool.false_eq_true, ite_false, ite_true,
    movingFrequencyCoefficient_bulk_action value outside μ childBound pivotBound V
      _ φ G n m _ small slot e _ _ _ hsmall]

end Ostmann

end OAI
