import OAI.Analysis.Laughlin.Polynomial.SymmetricTensorRange

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators

 theorem tensorWeight_product {R : Type*} [CommMonoid R] (Q : ℕ) (a : Fin Q → Fin 2) (x y : R) :
    (∏ i, if a i=1 then y else x) = y^(tensorWeight Q a)*x^(Q-tensorWeight Q a) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hc : (Finset.univ.filter (fun i => ¬ a i=1)).card=Q-tensorWeight Q a := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin Q => a i=1)
    simp only [Finset.card_univ,Fintype.card_fin] at h
    change (Finset.univ.filter (fun i => ¬ a i=1)).card=Q-(tensorBits Q a).card
    unfold tensorBits
    omega
  rw [hc]
  rfl

 theorem tensorWeight_zero_iff (Q : ℕ) (a : Fin Q → Fin 2) :
    tensorWeight Q a=0 ↔ a=fun _ => 0 := by
  constructor
  · intro h
    have he : tensorBits Q a=∅ := Finset.card_eq_zero.mp h
    funext i
    have hn : a i ≠ 1 := by
      intro hi
      have hm : i ∈ tensorBits Q a := by simp [tensorBits,hi]
      rw [he] at hm
      exact Finset.notMem_empty _ hm
    apply Fin.ext
    have ha := (a i).isLt
    have hn' : (a i).val ≠ 1 := by intro he; exact hn (Fin.ext he)
    simp only [Fin.val_zero]
    omega
  · rintro rfl
    simp [tensorWeight,tensorBits]

 theorem symmetricTensor_zero_column (Q : ℕ) (a : Fin Q → Fin 2) :
    symmetricTensorInclusion Q a 0 = if a=(fun _ => 0) then 1 else 0 := by
  simp [symmetricTensorInclusion,symmetricTensorInclusionReal,tensorWeight_zero_iff,apply_ite]

 theorem tensorMatrix_diagonal (Q : ℕ) (x y : ℂ) :
    tensorMatrix Q (Matrix.diagonal (fun i : Fin 2 => if i=0 then x else y)) =
      Matrix.diagonal (fun a => y^(tensorWeight Q a)*x^(Q-tensorWeight Q a)) := by
  classical
  ext a b
  by_cases hab : a=b
  · subst b
    simp only [tensorMatrix,Matrix.diagonal_apply_eq]
    have he (i : Fin Q) : (if a i=0 then x else y)=(if a i=1 then y else x) := by
      have h : a i=0 ∨ a i=1 := by omega
      rcases h with h | h <;> simp [h]
    simp_rw [he]
    exact tensorWeight_product Q a x y
  · rw [Matrix.diagonal_apply_ne _ hab]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

end Laughlin.Rotation

end OAI
