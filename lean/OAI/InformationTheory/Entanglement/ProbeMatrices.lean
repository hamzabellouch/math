import OAI.InformationTheory.Entanglement.ProbeDensity

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix MeasureTheory Filter
namespace SecretKey
open ChannelCompletion
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
def marginalLeft (W : Mat (n×m)) : Mat n := fun i j => ∑ a, W (i,a) (j,a)
def marginalRight (W : Mat (n×m)) : Mat m := fun a b => ∑ i, W (i,a) (i,b)
omit [DecidableEq n] [DecidableEq m] in
lemma marginalLeft_psd {W : Mat (n×m)} (hW : W.PosSemidef) : (marginalLeft W).PosSemidef :=
  partial_trace_psd hW
omit [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma marginalRight_psd {W : Mat (n×m)} (hW : W.PosSemidef) : (marginalRight W).PosSemidef := by
  have he : marginalRight W=∑ i, W.submatrix (fun a => (i,a)) (fun a => (i,a)) := by ext a b; simp [marginalRight,Matrix.sum_apply,Matrix.submatrix_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun i _ => hW.submatrix _)
omit [DecidableEq n] in
lemma trace_test_left (E : Mat n) (W : Mat (n×m)) :
    Matrix.trace (E*marginalLeft W)=Matrix.trace ((E ⊗ₖ (1 : Mat m))*W) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,marginalLeft,Matrix.kronecker_apply,
    Fintype.sum_prod_type,Matrix.one_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
omit [DecidableEq m] in
lemma trace_test_right (G : Mat m) (W : Mat (n×m)) :
    Matrix.trace (G*marginalRight W)=Matrix.trace (((1 : Mat n) ⊗ₖ G)*W) := by
  have hh (i : n) (a : m) :
      (∑ k : n, ∑ b : m, if i=k then G a b*W (k,b) (i,a) else 0)=
        ∑ b : m, G a b*W (i,b) (i,a) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,marginalRight,Matrix.kronecker_apply,
    Fintype.sum_prod_type,Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.mul_sum]
  change (∑ a : m, ∑ b : m, ∑ i : n, G a b*W (i,b) (i,a))=
    ∑ i : n, ∑ a : m, ∑ k : n, ∑ b : m, if i=k then G a b*W (k,b) (i,a) else 0
  simp_rw [hh]
  calc
    _=∑ a : m, ∑ i : n, ∑ b : m, G a b*W (i,b) (i,a) :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _=_ := Finset.sum_comm
end SecretKey

end

end OAI
