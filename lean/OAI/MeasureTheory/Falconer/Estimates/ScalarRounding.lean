import OAI.MeasureTheory.Falconer.Estimates.ScalarPointPaths

namespace OAI

/-! Rounding an actual separated scalar set to dyadic centers preserves
 its cardinality and moves each point by at most half a fine cell. -/
namespace Falconer.Regularization

noncomputable def scalarPointLeaves (N : ℕ) (X : Finset ℝ) : Finset (CellPath 1) :=
  X.image (scalarPointPath N)

noncomputable def scalarRoundedPoints (N : ℕ) (X : Finset ℝ) : Finset ℝ :=
  (scalarPointLeaves N X).image scalarPathCenter

 theorem scalarPointLeaves_subset (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1) : scalarPointLeaves N X ⊆ cubePaths 1 N := by
  intro p hp
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  exact scalarPointPath_mem N (hX x hx)

 theorem scalarPointLeaves_card (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (1/2:ℝ)^N ≤ |x-y|) :
    (scalarPointLeaves N X).card = X.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy heq
  by_contra hne
  exact (not_lt_of_ge (hsep x hx y hy hne)) (scalar_point_path_same (hX x hx) (hX y hy) heq)

 theorem scalarRoundedPoints_eq_image (N : ℕ) (X : Finset ℝ) :
    scalarRoundedPoints N X = X.image (fun x => scalarPathCenter (scalarPointPath N x)) := by
  simp only [scalarRoundedPoints,scalarPointLeaves,Finset.image_image,Function.comp_def]

 theorem scalarRoundedPoints_card (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → (1/2:ℝ)^N ≤ |x-y|) :
    (scalarRoundedPoints N X).card = X.card := by
  exact (scalar_leaf_center_card _ (scalarPointLeaves_subset N X hX)).trans
    (scalarPointLeaves_card N X hX hsep)

 theorem scalarRoundedPoints_near (N : ℕ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 0 ≤ x ∧ x < 1) :
    ∀ y ∈ scalarRoundedPoints N X, ∃ x ∈ X, |y-x| ≤ (1/2:ℝ)^N/2 := by
  rw [scalarRoundedPoints_eq_image]
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact ⟨x,hx,by simpa only [abs_sub_comm] using scalar_point_path_error N (hX x hx)⟩

end Falconer.Regularization

end OAI
