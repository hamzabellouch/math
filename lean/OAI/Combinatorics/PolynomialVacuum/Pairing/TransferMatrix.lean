import OAI.Combinatorics.PolynomialVacuum.Pairing.RowKernel
import OAI.Combinatorics.PolynomialVacuum.Algebra.RowEigenvector

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

 

noncomputable def honeycombKernel : (N : ℕ) → (Fin N → Spin) → (Fin N → Spin) → Spin → Spin → ℂ
  | 0,_,_,a,b => if b=a then 1 else 0
  | N+1,out,inp,a,b => ∑ h : Spin, ∑ k : Spin,
      honeycombPiece (out 0,h) (a,inp 0) k *
        honeycombKernel N (Fin.tail out) (Fin.tail inp) h b

noncomputable def physicalTransfer (N : ℕ) (κ : ℂ) :
    Matrix (Fin N → Spin) (Fin N → Spin) ℂ :=
  fun out inp => ∑ h : Spin,κ^charge h * honeycombKernel N out inp h h

theorem rowKernel_honeycomb (N : ℕ) (out inp : Fin N → Spin) (a b : Spin) :
    rowKernel N t (fun _ => 1) out inp a b=
      exchangeDenominator t 1^N*honeycombKernel N out inp a b := by
  induction N generalizing a b with
  | zero => simp [rowKernel,honeycombKernel]
  | succ N ih =>
    simp only [rowKernel,honeycombKernel]
    have hs : skipOne 0 (fun _ : ℕ => (1 : ℂ))=fun _ => 1 := by funext j; rfl
    simp only [hs,ih,honeycomb_entry_exact,honeycombEntry,Finset.sum_mul,Finset.mul_sum,pow_succ]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem transferMatrix_physical (N : ℕ) :
    transferMatrix N zeta t (fun _ => 1)=exchangeDenominator t 1^N • physicalTransfer N zeta := by
  funext out inp
  simp only [transferMatrix,rowKernel_honeycomb,physicalTransfer,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

noncomputable def physicalPolynomialVector (N : ℕ) : (Fin N → Spin) → ℂ :=
  fun s => MvPolynomial.eval (fun _ => 1) (polynomialVacuum N s)

theorem homogeneousVector_finiteTensor (N : ℕ) :
    homogeneousVector N=finiteTensor N (physicalPolynomialVector N) := rfl

theorem finiteTensor_restrict (N : ℕ) (f : (Fin N → Spin) → ℂ) (s : Fin N → Spin) :
    finiteTensor N f (fun j => if h : j<N then s ⟨j,h⟩ else .zero)=f s := by
  unfold finiteTensor
  congr 1
  funext j
  simp [j.isLt]

theorem honeycombDenominator_ne_zero : exchangeDenominator t 1≠0 := by
  have ht : (t^2*t)^4= -1 := by dsimp [t]; vacuum_ring_finish
  have hT : T*t= -1 := by dsimp [T,t]; vacuum_ring_finish
  unfold exchangeDenominator
  apply mul_ne_zero
  · intro hz
    have hh : t^2*t=1 := sub_eq_zero.mp hz
    rw [hh] at ht
    norm_num at ht
  · rw [hT]
    norm_num

 

theorem physicalPolynomialVector_eigen (N : ℕ) (s : Fin N → Spin) :
    (physicalTransfer N zeta).mulVec (physicalPolynomialVector N) s=physicalPolynomialVector N s := by
  let sn : ℕ → Spin:=fun j => if h : j<N then s ⟨j,h⟩ else .zero
  have he:=congrFun (polynomialVacuum_honeycombRow N) sn
  rw [homogeneousVector_finiteTensor,tracedTrain_matrix,transferMatrix_physical] at he
  simp only [Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,mul_assoc] at he
  have hs : (fun j : Fin N => sn j.val)=s := by funext j; simp [sn,j.isLt]
  rw [hs,finiteTensor_restrict] at he
  rw [← Finset.mul_sum] at he
  apply (mul_left_cancel₀ (pow_ne_zero N honeycombDenominator_ne_zero))
  simpa only [Matrix.mulVec,dotProduct,mul_assoc] using he

end PolynomialVacuumAlgebra

end OAI
