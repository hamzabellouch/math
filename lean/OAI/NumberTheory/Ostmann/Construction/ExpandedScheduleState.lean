import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduledTemplate

namespace OAI

/-! # Updating a fresh pivot coordinate performs the original atom reconstruction -/

namespace Ostmann

open scoped Classical

/-- Expose the child assignment with any decidable equality instance. -/
theorem wordTransferLeftState_node {σ : Type*} [DecidableEq σ] {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ) (P : ℕ) :
    (wordTransferSystem σ).leftState ((WordTransferTemplate.node d l r).state x) P =
      l.state (Function.update x d.target P) := by
  change (⟨n, l, _⟩ : WordTransferState σ) = ⟨n, l, _⟩
  congr 2
  funext i
  by_cases hi : i = d.target <;> simp only [Function.update_apply, hi, ite_true, ite_false]

theorem wordTransferRightState_node {σ : Type*} [DecidableEq σ] {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ) (P : ℕ) :
    (wordTransferSystem σ).rightState ((WordTransferTemplate.node d l r).state x) P =
      r.state (Function.update x d.target P) := by
  change (⟨n, r, _⟩ : WordTransferState σ) = ⟨n, r, _⟩
  congr 2
  funext i
  by_cases hi : i = d.target <;> simp only [Function.update_apply, hi, ite_true, ite_false]

theorem word_product_update_of_fresh {σ : Type*} [DecidableEq σ] (word : List σ) (x : σ → ℕ)
    (pivot : σ) (P : ℕ) (hfresh : ∀ i ∈ word, i ≠ pivot) :
    (word.map (Function.update x pivot P)).prod = (word.map x).prod := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact Function.update_of_ne (hfresh i hi) P x

/-- At the reconstructed pivot we read P, at H the selected copy, and at
Y the common retained value. This equality includes composite atom words. -/
theorem reverseCopyLabelMap_product_update {I σ : Type*} [DecidableEq σ] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (P : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List σ) (x : σ → ℕ)
    (hfresh : ∀ i j, j ∈ current i → j ≠ pivot) (i : CopyScheduleAtoms role n) :
    ((reverseCopyLabelMap role n b [pivot] current i).map (Function.update x pivot P)).prod =
      reverseCopyLabelMap role n b P (fun j => ((current j).map x).prod) i := by
  unfold reverseCopyLabelMap
  split_ifs
  · exact word_product_update_of_fresh _ x pivot P (hfresh _)
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Function.update_self, mul_one]
  · exact word_product_update_of_fresh _ x pivot P (hfresh _)

/-- The inserted coordinate does not alter any of the actual H-copy
products that enter the reversing numerator. -/
theorem expandedHWord_product_update {I σ : Type*} [Fintype I] [DecidableEq σ] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (x : σ → ℕ) (pivot : σ) (P : ℕ) (hfresh : ∀ i j, j ∈ current i → j ≠ pivot) :
    ((expandedHWord role n b current).map (Function.update x pivot P)).prod =
      ((expandedHWord role n b current).map x).prod := by
  rw [expandedHWord_product, expandedHWord_product]
  apply Finset.prod_congr rfl
  intro i _
  exact word_product_update_of_fresh _ x pivot P (hfresh _)

end Ostmann

end OAI
