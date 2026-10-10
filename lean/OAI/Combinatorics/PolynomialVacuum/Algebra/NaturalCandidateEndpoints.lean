import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolationNodes
import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupZeroNode

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem liftState_params_congr {n : ℕ} (ψ : State n) (X Y : ℕ → ℂ)
    (h : ∀ j < n, X j=Y j) : liftState ψ X=liftState ψ Y := by
  have he : (fun j : Fin n => X j.val)=(fun j : Fin n => Y j.val) := by
    funext j; exact h j j.isLt
  funext s
  simp only [liftState,liftPolyTensor,he]

theorem interpolateState_node_natural {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hψ : LowerExchange (liftState ψ) n) (i : ℕ) (hi : i ≤ n)
    (X : ℕ → ℂ) (hX : X (n+1)=T*X i) :
    liftState (interpolateState ψ χ) X=naturalPrescription (liftState ψ) n i X := by
  rw [← cupPrescription_evaluation ψ ⟨i,by omega⟩ X]
  funext s
  exact interpolateState_node ψ χ hψ (fun j => s j.val) (fun j => X j.val)
    ⟨i,by omega⟩ hX

theorem interpolateState_lastZero {n : ℕ} (ψ : State n) (χ : State (n+1)) :
    LastZeroReduction (liftState (interpolateState ψ χ)) (liftState χ) (n+1) := by
  intro X s hX hs
  cases he : s (n+1) with
  | plus => exact False.elim (hs he)
  | minus =>
    change eval (fun j : Fin (n+2) => X j.val) (interpolateState ψ χ (fun j => s j.val))=0
    exact interpolateState_minus_zero ψ χ (fun j => s j.val) (fun j => X j.val) he hX
  | zero =>
    simp only [ite_true]
    simpa [prefixProduct,Fin.prod_univ_eq_prod_range,liftState,liftPolyTensor,Function.comp_def] using
      interpolateState_zero_reduction ψ χ (fun j => s j.val) (fun j => X j.val) he hX

end PolynomialVacuumAlgebra

end OAI
