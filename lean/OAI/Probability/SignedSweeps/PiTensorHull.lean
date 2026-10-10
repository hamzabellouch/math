import OAI.Probability.SignedSweeps.PiTensorMatrix

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {J : Type*} [Fintype J] {I : J → Type*} [∀ j, Fintype (I j)]

omit [∀ index, Fintype (I index)] in
lemma piTensorMatrix_update [∀ index, Fintype (I index)]
    (A : ∀ j, Matrix (I j) (I j) ℂ) (j : J)
    (X : Matrix (I j) (I j) ℂ) (w z : ∀ j, I j) :
    piTensorMatrix (Function.update A j X) w z =
      X (w j) (z j) * ∏ k ∈ Finset.univ.erase j, A k (w k) (z k) := by
  unfold piTensorMatrix
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

def piTensorMatrixSlot (A : ∀ j, Matrix (I j) (I j) ℂ) (j : J) :
    Matrix (I j) (I j) ℂ →ₗ[ℝ] Matrix (∀ j, I j) (∀ j, I j) ℂ where
  toFun X := piTensorMatrix (Function.update A j X)
  map_add' X Y := by
    ext w z
    simp only [piTensorMatrix_update, Matrix.add_apply]
    exact add_mul _ _ _
  map_smul' a X := by
    ext w z
    simp only [piTensorMatrix_update, Matrix.smul_apply, RingHom.id_apply]
    exact smul_mul_assoc _ _ _

lemma piTensorMatrix_slot_mem (A : ∀ j, Matrix (I j) (I j) ℂ) (j : J)
    {S : Set (Matrix (I j) (I j) ℂ)} {C : Set (Matrix (∀ j, I j) (∀ j, I j) ℂ)}
    (hC : IsClosed C) (hV : Convex ℝ C)
    (hS : ∀ X ∈ S, piTensorMatrix (Function.update A j X) ∈ C)
    (hA : A j ∈ closedConvexHull ℝ S) : piTensorMatrix A ∈ C := by
  have hu : piTensorMatrixSlot A j (A j) = piTensorMatrix A := by
    change piTensorMatrix (Function.update A j (A j)) = piTensorMatrix A
    rw [Function.update_eq_self]
  rw [← hu]
  exact closedConvexHull_min (t := (piTensorMatrixSlot A j) ⁻¹' C) hS
    (hV.linear_preimage (piTensorMatrixSlot A j))
    (hC.preimage (piTensorMatrixSlot A j).continuous_of_finiteDimensional) hA

lemma piTensorMatrix_mem_closed_convex
    (S : ∀ j, Set (Matrix (I j) (I j) ℂ))
    {C : Set (Matrix (∀ j, I j) (∀ j, I j) ℂ)}
    (hC : IsClosed C) (hV : Convex ℝ C)
    (hS : ∀ A : ∀ j, Matrix (I j) (I j) ℂ, (∀ j, A j ∈ S j) → piTensorMatrix A ∈ C)
    (A : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, A j ∈ closedConvexHull ℝ (S j)) : piTensorMatrix A ∈ C := by
  have hh (s : Finset J) : ∀ A : ∀ j, Matrix (I j) (I j) ℂ,
      (∀ j ∈ s, A j ∈ closedConvexHull ℝ (S j)) →
      (∀ j ∉ s, A j ∈ S j) → piTensorMatrix A ∈ C := by
    induction s using Finset.induction_on with
    | empty =>
      intro A _ h
      exact hS A (fun j => h j (Finset.notMem_empty j))
    | @insert j s hj ih =>
      intro A hA ho
      apply piTensorMatrix_slot_mem A j hC hV _ (hA j (Finset.mem_insert_self _ _))
      intro X hX
      apply ih
      · intro k hk
        have hkj : k ≠ j := fun he => hj (he ▸ hk)
        rw [Function.update_of_ne hkj]
        exact hA k (Finset.mem_insert_of_mem hk)
      · intro k hk
        by_cases hkj : k = j
        · subst k
          simpa only [Function.update_self] using hX
        · rw [Function.update_of_ne hkj]
          exact ho k (by simp only [Finset.mem_insert, not_or]; exact ⟨hkj,hk⟩)
  exact hh Finset.univ A (fun j _ => hA j) (fun j hj => False.elim (hj (Finset.mem_univ j)))

lemma piTensorMatrix_closed_hull
    (S : ∀ j, Set (Matrix (I j) (I j) ℂ))
    (A : ∀ j, Matrix (I j) (I j) ℂ)
    (hA : ∀ j, A j ∈ closedConvexHull ℝ (S j)) :
    piTensorMatrix A ∈ closedConvexHull ℝ
      {P | ∃ R : ∀ j, Matrix (I j) (I j) ℂ, (∀ j, R j ∈ S j) ∧ piTensorMatrix R = P} := by
  apply piTensorMatrix_mem_closed_convex S isClosed_closedConvexHull convex_closedConvexHull _ A hA
  intro R hR
  exact subset_closedConvexHull ⟨R,hR,rfl⟩

end SignedSweeps
end

end OAI
