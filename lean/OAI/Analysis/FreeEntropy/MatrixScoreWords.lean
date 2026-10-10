import OAI.Analysis.FreeEntropy.FisherVariational

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def matrixScoreWord (w : List (Fin n)) (j k : Fin d) (x : MatrixIndex n d → ℝ) : ℂ :=
    Matrix.trace (hermitianBasis j k*matrixWord (coordinateMatrix x) w)
 theorem matrixScoreWord_polynomial (w : List (Fin n)) (j k : Fin d) :
    IsComplexPolynomial (matrixScoreWord w j k) :=
  ((IsMatrixPolynomial.const (hermitianBasis j k)).mul
    (IsMatrixPolynomial.word (fun i a b => coordinateMatrix_polynomial i a b) w)).trace
 theorem matrixScoreWord_derivative (w : List (Fin n)) (i : Fin n) (j k : Fin d) (x : MatrixIndex n d → ℝ) :
    complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x =
      ∑r : Fin w.length, if w[r.val]=i then
        Matrix.trace (hermitianBasis j k*matrixWord (coordinateMatrix x) (w.take r.val)*hermitianBasis j k*
          matrixWord (coordinateMatrix x) (w.drop (r.val+1))) else 0 := by
  have hd := hasDerivAt_matrix_mul
    (A := fun _ : ℝ => hermitianBasis j k) (A' := 0)
    (fun a b => hasDerivAt_const (x (i,j,k)) (hermitianBasis j k a b))
    (hasDerivAt_matrixWord (coordinateMatrix_hasDeriv x (i,j,k)) w)
  have ht := HasDerivAt.sum (u := univ) (fun a _ => hd a a)
  have he := ht.deriv
  simp only [Finset.sum_fn] at he
  change complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x = _ at he
  rw [he]
  simp only [Function.update_eq_self,zero_mul,zero_add,Matrix.mul_apply,Matrix.add_apply,
    Matrix.zero_apply,zero_mul,zero_add]
  change Matrix.trace (hermitianBasis j k*matrixWordVariation (coordinateMatrix x)
    (fun a => if i=a then hermitianBasis j k else 0) w) = _
  rw [matrixWordVariation,mul_sum,Matrix.trace_sum]
  apply sum_congr rfl
  intro r _
  by_cases h : w[r.val]=i
  · simp [h,mul_assoc]
  · simp [h,Ne.symm h]
 theorem hermitianBasis_contract_trace (U V : Matrix (Fin d) (Fin d) ℂ) :
    (∑j,∑k,Matrix.trace (hermitianBasis j k*U*hermitianBasis j k*V)) = Matrix.trace U*Matrix.trace V := by
  calc
    _ = Matrix.trace ((∑j,∑k,hermitianBasis j k*U*hermitianBasis j k)*V) := by
      simp only [sum_mul,Matrix.trace_sum]
    _ = _ := by rw [hermitianBasis_contract,smul_mul_assoc,one_mul,Matrix.trace_smul,smul_eq_mul]
 theorem matrixScoreWord_divergence (w : List (Fin n)) (i : Fin n) (x : MatrixIndex n d → ℝ) :
    (∑j,∑k,complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x) =
      ∑r : Fin w.length, if w[r.val]=i then
        Matrix.trace (matrixWord (coordinateMatrix x) (w.take r.val))*
          Matrix.trace (matrixWord (coordinateMatrix x) (w.drop (r.val+1))) else 0 := by
  simp_rw [matrixScoreWord_derivative]
  have hreorder (f : Fin d → Fin d → Fin w.length → ℂ) :
      (∑j,∑k,∑r,f j k r) = ∑r,∑j,∑k,f j k r := by
    calc
      _ = ∑j,∑r,∑k,f j k r := sum_congr rfl (fun j _ => sum_comm)
      _ = _ := sum_comm
  rw [hreorder]
  apply sum_congr rfl
  intro r _
  by_cases h : w[r.val]=i
  · simp only [h,ite_true]
    exact hermitianBasis_contract_trace _ _
  · simp [h]
 def matrixPolynomial (p : WordPolynomial n) (A : Fin n → Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
    p.sum (fun w c => c • matrixWord A w)
 def matrixScorePolynomial (p : WordPolynomial n) (j k : Fin d) (x : MatrixIndex n d → ℝ) : ℂ :=
    Matrix.trace (hermitianBasis j k*matrixPolynomial p (coordinateMatrix x))
 theorem matrixScorePolynomial_sum (p : WordPolynomial n) (j k : Fin d) (x : MatrixIndex n d → ℝ) :
    matrixScorePolynomial p j k x = ∑w∈p.support,p w*matrixScoreWord w j k x := by
  simp only [matrixScorePolynomial,matrixPolynomial,Finsupp.sum,mul_sum,mul_smul_comm,
    Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul,matrixScoreWord]
 theorem matrixScorePolynomial_polynomial (p : WordPolynomial n) (j k : Fin d) :
    IsComplexPolynomial (matrixScorePolynomial p j k) := by
  have he : matrixScorePolynomial p j k = fun x => ∑w∈p.support,p w*matrixScoreWord w j k x := funext (matrixScorePolynomial_sum p j k)
  rw [he]
  exact IsComplexPolynomial.finset_sum p.support (fun w _ => (matrixScoreWord_polynomial w j k).const_mul (p w))
 theorem matrixScorePolynomial_divergence (p : WordPolynomial n) (i : Fin n) (x : MatrixIndex n d → ℝ) :
    (∑j,∑k,complexCoordinateDerivative (matrixScorePolynomial p j k) (i,j,k) x) =
      ∑w∈p.support,p w*∑r : Fin w.length, if w[r.val]=i then
        Matrix.trace (matrixWord (coordinateMatrix x) (w.take r.val))*
          Matrix.trace (matrixWord (coordinateMatrix x) (w.drop (r.val+1))) else 0 := by
  have he j k : complexCoordinateDerivative (matrixScorePolynomial p j k) (i,j,k) x =
      ∑w∈p.support,p w*complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x := by
    have hd := HasDerivAt.sum (u := p.support) (fun w _ => ((matrixScoreWord_polynomial w j k).hasDerivAt (i,j,k) x).const_mul (p w))
    simpa only [complexCoordinateDerivative,matrixScorePolynomial_sum,Finset.sum_fn] using hd.deriv
  simp_rw [he]
  calc
    _ = ∑w∈p.support,p w*(∑j,∑k,complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x) := by
      simp_rw [mul_sum]
      calc
        _ = ∑j,∑w∈p.support,∑k,p w*complexCoordinateDerivative (matrixScoreWord w j k) (i,j,k) x :=
          sum_congr rfl (fun j _ => sum_comm)
        _ = _ := sum_comm
    _ = _ := by simp_rw [matrixScoreWord_divergence]
end FiniteEntropySeparation

end

end OAI
