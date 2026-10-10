import OAI.Analysis.FreeEntropy.GUEBounds

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Classical
namespace FiniteEntropySeparation
 variable {α : Type u1} {n d : ℕ}
 theorem basis_trace_contract (P Q : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, Matrix.trace (hermitianBasis j k*P*hermitianBasis j k*Q)) = Matrix.trace P*Matrix.trace Q := by
  simp_rw [← Matrix.trace_sum, ← sum_mul]
  rw [hermitianBasis_contract, smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul]
 theorem fixedTraceWord_polynomial (A : α → Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n)) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => Matrix.trace (B*matrixWord (jointMatrix A x) w)) :=
   ((IsMatrixPolynomial.const B).mul (IsMatrixPolynomial.word (jointMatrix_polynomial A) w)).trace
 theorem fixedTraceWord_derivative (A : α → Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (w : List (α ⊕ Fin n)) (q : MatrixIndex n d) (x : MatrixIndex n d → ℝ) :
    complexCoordinateDerivative (fun y => Matrix.trace (B*matrixWord (jointMatrix A y) w)) q x =
      (Real.sqrt d:ℂ)⁻¹ * ∑ r : Fin w.length, if w[r.val]=Sum.inr q.1 then
        Matrix.trace (B*matrixWord (jointMatrix A x) (w.take r.val)*hermitianBasis q.2.1 q.2.2*matrixWord (jointMatrix A x) (w.drop (r.val+1))) else 0 := by
  have hm := hasDerivAt_matrix_mul (fun j k => hasDerivAt_const (x q) (B j k)) (hasDerivAt_matrixWord (jointMatrix_hasDeriv A x q) w)
  have ht := HasDerivAt.sum (u := univ) (fun j _ => hm j j)
  have htrace : HasDerivAt (fun y => Matrix.trace (B*matrixWord (jointMatrix A (Function.update x q y)) w))
      (Matrix.trace (B*matrixWordVariation (jointMatrix A (Function.update x q (x q))) (noiseDirection q) w)) (x q) := by
    simpa only [Finset.sum_fn, Matrix.trace, Matrix.diag, show (fun _ _ : Fin d => (0:ℂ)) = (0:Matrix (Fin d) (Fin d) ℂ) from rfl, Matrix.zero_mul, zero_add] using ht
  have he := htrace.deriv
  change complexCoordinateDerivative (fun y => Matrix.trace (B*matrixWord (jointMatrix A y) w)) q x = _ at he
  simp only [Function.update_eq_self] at he
  rw [he]
  change Matrix.trace (B*matrixWordVariation (jointMatrix A x) (noiseDirection q) w) = _
  simp only [matrixWordVariation, mul_sum, Matrix.trace_sum]
  apply sum_congr rfl
  intro r _
  simp only [noiseDirection]
  split_ifs <;> simp [Matrix.trace_smul, mul_assoc]
 theorem gueTraceWord_expand (A : α → Matrix (Fin d) (Fin d) ℂ) (i : Fin n) (w : List (α ⊕ Fin n)) (x : MatrixIndex n d → ℝ) :
    matrixTraceWord (jointMatrix A x) (Sum.inr i::w) =
      ((d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹)*∑ j, ∑ k, (x (i,j,k):ℂ)*Matrix.trace (hermitianBasis j k*matrixWord (jointMatrix A x) w) := by
  simp only [matrixTraceWord, matrixWord_cons, jointMatrix, Sum.elim_inr, gueMatrix, coordinateMatrix_expand,
    smul_mul_assoc, sum_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, mul_sum]
  ring_nf
 theorem gueTraceWord_stein (_hd : 0 < d) (A : α → Matrix (Fin d) (Fin d) ℂ) (i : Fin n) (w : List (α ⊕ Fin n)) :
    (∫ x, matrixTraceWord (jointMatrix A x) (Sum.inr i::w) ∂productGaussian (MatrixIndex n d)) =
      ∑ r : Fin w.length, if w[r.val]=Sum.inr i then
        ∫ x, matrixTraceWord (jointMatrix A x) (w.take r.val)*matrixTraceWord (jointMatrix A x) (w.drop (r.val+1)) ∂productGaussian (MatrixIndex n d) else 0 := by
  let F := fun (j k : Fin d) (x : MatrixIndex n d → ℝ) => Matrix.trace (hermitianBasis j k*matrixWord (jointMatrix A x) w)
  have hF (j k : Fin d) : IsComplexPolynomial (F j k) := fixedTraceWord_polynomial A _ w
  have hi (j k : Fin d) := ((IsComplexPolynomial.coord (i,j,k)).mul (hF j k)).integrable
  have hdF (j k : Fin d) := ((hF j k).derivative (i,j,k)).integrable
  simp_rw [gueTraceWord_expand]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hi _ k)]
  change ((d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹)*(∑ j, ∑ k, ∫ x, (x (i,j,k):ℂ)*F j k x ∂productGaussian (MatrixIndex n d)) = _
  simp_rw [(hF _ _).stein]
  simp_rw [← integral_finsetSum _ (fun k _ => hdF _ k)]
  rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hdF j k))]
  have hcalc (x : MatrixIndex n d → ℝ) : (∑ j, ∑ k, complexCoordinateDerivative (F j k) (i,j,k) x) =
      (Real.sqrt d:ℂ)⁻¹ * ∑ r : Fin w.length, if w[r.val]=Sum.inr i then
        Matrix.trace (matrixWord (jointMatrix A x) (w.take r.val))*Matrix.trace (matrixWord (jointMatrix A x) (w.drop (r.val+1))) else 0 := by
    simp only [F, fixedTraceWord_derivative]
    simp_rw [← mul_sum]
    congr 1
    have hs : ∀ j : Fin d, (∑ k : Fin d, ∑ r : Fin w.length, if w[r.val]=Sum.inr i then
        Matrix.trace (hermitianBasis j k*matrixWord (jointMatrix A x) (w.take r.val)*hermitianBasis j k*matrixWord (jointMatrix A x) (w.drop (r.val+1))) else 0) =
        ∑ r : Fin w.length, ∑ k : Fin d, if w[r.val]=Sum.inr i then
        Matrix.trace (hermitianBasis j k*matrixWord (jointMatrix A x) (w.take r.val)*hermitianBasis j k*matrixWord (jointMatrix A x) (w.drop (r.val+1))) else 0 := fun _ => sum_comm
    simp_rw [hs]
    rw [sum_comm]
    apply sum_congr rfl
    intro r _
    simp only [sum_ite_irrel, sum_const_zero]
    split_ifs
    · exact basis_trace_contract _ _
    · rfl
  simp_rw [hcalc]
  rw [integral_const_mul, ← mul_assoc]
  have hc : (d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹*(Real.sqrt d:ℂ)⁻¹=(d:ℂ)⁻¹*(d:ℂ)⁻¹ := by
    rw [mul_assoc, ← pow_two, inv_pow]
    have hs : (Real.sqrt d:ℂ)^2=(d:ℂ) := by norm_cast; exact Real.sq_sqrt (Nat.cast_nonneg _)
    rw [hs]
  rw [hc]
  have hp (r : Fin w.length) := ((IsMatrixPolynomial.word (jointMatrix_polynomial A) (w.take r.val)).trace.mul
    (IsMatrixPolynomial.word (jointMatrix_polynomial A) (w.drop (r.val+1))).trace).integrable
  rw [integral_finsetSum _ (fun r _ => by split_ifs <;> first | exact hp r | exact integrable_const 0)]
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  split_ifs with h
  · simp only [matrixTraceWord]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  · simp
end FiniteEntropySeparation

end

end OAI
