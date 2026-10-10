import OAI.Combinatorics.PolynomialVacuum.Pairing.RowPeriodic

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical
section MatrixPaths
variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def matrixPathWeight (A : Matrix S S ℂ) {H : ℕ} (inp : S) (r : Fin H → S) : ℂ :=
  ∏j : Fin H,A (r j) ((Fin.cons inp r : Fin (H+1) → S) j.castSucc)

def matrixPathEnd {H : ℕ} (inp : S) (r : Fin H → S) : S :=
  (Fin.cons inp r : Fin (H+1) → S) (Fin.last H)

omit [Fintype S] [DecidableEq S] in
@[simp] theorem matrixPathEnd_cons [Fintype S] [DecidableEq S] {H : ℕ} (inp h : S) (r : Fin H → S) :
    matrixPathEnd inp (Fin.cons h r)=matrixPathEnd h r := rfl

omit [Fintype S] [DecidableEq S] in
@[simp] theorem matrixPathWeight_cons [Fintype S] [DecidableEq S] (A : Matrix S S ℂ) {H : ℕ} (inp h : S) (r : Fin H → S) :
    matrixPathWeight A inp (Fin.cons h r)=A h inp*matrixPathWeight A h r := by
  unfold matrixPathWeight
  rw [Fin.prod_univ_succ]
  congr 1

 
theorem matrix_pow_path_sum (A : Matrix S S ℂ) (H : ℕ) (out inp : S) :
    (A^H) out inp=∑r : Fin H → S,
      if matrixPathEnd inp r=out then matrixPathWeight A inp r else 0 := by
  induction H generalizing out inp with
  | zero => simp [matrixPathEnd,matrixPathWeight,Matrix.one_apply,eq_comm]
  | succ H ih =>
    rw [pow_succ,Matrix.mul_apply]
    simp_rw [ih]
    rw [← (Fin.consEquiv (fun _ : Fin (H+1) => S)).sum_comp,Fintype.sum_prod_type]
    change _ = ∑h : S,∑r : Fin H → S,
      if matrixPathEnd inp (Fin.cons h r)=out then matrixPathWeight A inp (Fin.cons h r) else 0
    simp only [matrixPathEnd_cons,matrixPathWeight_cons,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> simp [mul_comm]
end MatrixPaths

 

theorem physicalTransfer_pow_local (N H : ℕ) (κ : ℂ) (out inp : Fin (N+1) → Spin) :
    (physicalTransfer (N+1) κ^H) out inp=
      ∑r : Fin H → (Fin (N+1) → Spin),
      if matrixPathEnd inp r=out then
        ∏j : Fin H,∑a : Fin (N+1) → Spin,∑k : Fin (N+1) → Spin,
          κ^charge (a (Fin.last N))*∏i : Fin (N+1),
            honeycombPiece (r j i,a i)
              (a (i-1),(Fin.cons inp r : Fin (H+1) → (Fin (N+1) → Spin)) j.castSucc i) (k i)
      else 0 := by
  rw [matrix_pow_path_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · simp only [matrixPathWeight,physicalTransfer_periodic]
  · rfl

end PolynomialVacuumAlgebra

end OAI
