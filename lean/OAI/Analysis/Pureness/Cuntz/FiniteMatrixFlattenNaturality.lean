import OAI.Analysis.Pureness.Cuntz.FiniteMatrixFlatten

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finiteMatrixFlatten_inclusion {k l : ℕ} (h : k ≤ l) (n : ℕ)
    (X : FinMatrix (FinMatrix A n) k) :
    finiteMatrixFlatten l n (matrixInclusion h X)=
      matrixInclusion (Nat.mul_le_mul_right n h) (finiteMatrixFlatten k n X) := by
  ext p q
  obtain ⟨⟨i,a⟩,rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j,b⟩,rfl⟩ := finProdFinEquiv.surjective q
  rw [finiteMatrixFlatten_entry]
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · let i0 : Fin k := ⟨i.val,hi⟩
      let j0 : Fin k := ⟨j.val,hj⟩
      have he (v : Fin k) (a : Fin n) :
          finProdFinEquiv (v.castLE h,a)=
            (finProdFinEquiv (v,a)).castLE (Nat.mul_le_mul_right n h) := by
        apply Fin.ext
        rfl
      have hi0 : i=i0.castLE h := rfl
      have hj0 : j=j0.castLE h := rfl
      rw [hi0,hj0,he,he,matrixInclusion_entry_inside,matrixInclusion_entry_inside,
        finiteMatrixFlatten_entry]
    · have hjbig : k*n ≤ (finProdFinEquiv (j,b)).val := by
        change k*n ≤ b.val+n*j.val
        calc
          k*n=n*k := Nat.mul_comm _ _
          _ ≤ n*j.val := Nat.mul_le_mul_left n (Nat.le_of_not_gt hj)
          _ ≤ b.val+n*j.val := Nat.le_add_left _ _
      rw [matrixInclusion_entry_outside h X i j (Or.inr (Nat.le_of_not_gt hj)),
        matrixInclusion_entry_outside _ _ _ _ (Or.inr hjbig)]
      rfl
  · have hibig : k*n ≤ (finProdFinEquiv (i,a)).val := by
      change k*n ≤ a.val+n*i.val
      calc
        k*n=n*k := Nat.mul_comm _ _
        _ ≤ n*i.val := Nat.mul_le_mul_left n (Nat.le_of_not_gt hi)
        _ ≤ a.val+n*i.val := Nat.le_add_left _ _
    rw [matrixInclusion_entry_outside h X i j (Or.inl (Nat.le_of_not_gt hi)),
      matrixInclusion_entry_outside _ _ _ _ (Or.inl hibig)]
    rfl

lemma finiteMatrixFlatten_scalar_one (n : ℕ) (M : FinMatrix A n) :
    finiteMatrixFlatten 1 n (scalarMatrixHom (ι := Fin 1) M)=
      matrixInclusion (show n ≤ 1*n from by omega) M := by
  ext p q
  obtain ⟨⟨i,a⟩,rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j,b⟩,rfl⟩ := finProdFinEquiv.surjective q
  fin_cases i
  fin_cases j
  rw [finiteMatrixFlatten_entry]
  have he (v : Fin n) : finProdFinEquiv ((0 : Fin 1),v)=
      v.castLE (show n ≤ 1*n from by omega) := by
    apply Fin.ext
    change v.val+n*0=v.val
    omega
  change M a b=matrixInclusion (show n ≤ 1*n from by omega) M
    (finProdFinEquiv ((0 : Fin 1),a)) (finProdFinEquiv ((0 : Fin 1),b))
  rw [he,he,matrixInclusion_entry_inside]
end CuntzPureness

end

end OAI
