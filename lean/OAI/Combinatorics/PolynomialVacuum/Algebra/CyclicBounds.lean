import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalRotation

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem rotatedPolynomial_degree {n : ℕ} (Ψ : State (n+1)) (s : ℕ → Spin) (j : ℕ) (hj : j<n) :
    (rotatedPolynomial Ψ s).degreeOf j=(Ψ (fun a => natRotate n s a.val)).degreeOf ⟨j+1,by omega⟩ := by
  have he := degreeOf_rename_of_injective (rotationIndex_injective n)
    ⟨j+1,by omega⟩ (p := Ψ (fun a => natRotate n s a.val))
  simpa only [rotatedPolynomial,rotationIndex,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel] using he

theorem cyclicDiscrepancy_degree {n : ℕ} (Ψ : State (n+1)) (d : ℕ)
    (hd : ∀ s i, (Ψ s).degreeOf i ≤ d) (s : ℕ → Spin) (j : ℕ) (hj : j<n) :
    (cyclicDiscrepancy Ψ s).degreeOf j ≤ d := by
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply dconst_mul
    rw [rotatedPolynomial_degree Ψ s j hj]
    exact hd _ _
  · rw [show (coordinatePolynomial Ψ s).degreeOf j=(Ψ (fun a => s a.val)).degreeOf ⟨j,by omega⟩ from
      coordinatePolynomial_degree Ψ s ⟨j,by omega⟩]
    exact hd _ _

theorem cyclicDiscrepancy_plus_degree {n : ℕ} (Ψ : State (n+1)) (d : ℕ)
    (hd : ∀ s i, s i=Spin.plus → (Ψ s).degreeOf i ≤ d)
    (s : ℕ → Spin) (j : ℕ) (hj : j<n) (hs : s j=Spin.plus) :
    (cyclicDiscrepancy Ψ s).degreeOf j ≤ d := by
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply dconst_mul
    rw [rotatedPolynomial_degree Ψ s j hj]
    exact hd _ _ (by simpa only [natRotate_succ] using hs)
  · rw [show (coordinatePolynomial Ψ s).degreeOf j=(Ψ (fun a => s a.val)).degreeOf ⟨j,by omega⟩ from
      coordinatePolynomial_degree Ψ s ⟨j,by omega⟩]
    exact hd _ _ hs

theorem cyclicDiscrepancy_minus_zero {n : ℕ} (Ψ : State (n+1)) (hz : MinusZero Ψ)
    (s : ℕ → Spin) (j : ℕ) (hj : j<n) (hs : s j=Spin.minus) : killSite j (cyclicDiscrepancy Ψ s)=0 := by
  apply MvPolynomial.funext
  intro X
  simp only [eval_killSite,map_zero,update_nat_decidable]
  let Y := Function.update X j 0
  change eval Y (cyclicDiscrepancy Ψ s)=0
  have h0 : liftState Ψ Y s=0 := eval_liftState_minusZero Ψ hz j (by omega) s Y hs (by simp [Y])
  have hr : liftState Ψ (natRotate n Y) (natRotate n s)=0 :=
    eval_liftState_minusZero Ψ hz (j+1) (by omega) _ _ (by simpa using hs) (by simp [Y])
  simp only [cyclicDiscrepancy,map_sub,map_mul,eval_C,eval_coordinatePolynomial,eval_rotatedPolynomial,h0,hr,mul_zero,sub_zero]

end PolynomialVacuumAlgebra

end OAI
