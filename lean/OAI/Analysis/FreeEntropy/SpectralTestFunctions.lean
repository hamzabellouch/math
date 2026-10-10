import OAI.Analysis.FreeEntropy.MatrixBlockEnergy

namespace OAI

noncomputable section
open Finset Filter
open scoped Topology ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def univariateMoment (m : List (Fin n) → ℂ) (q : Polynomial ℝ) (i : Fin n) : ℝ :=
    ∑k∈q.support,q.coeff k*(m (List.replicate k i)).re
 def commutatorMoment (m : List (Fin n) → ℂ) (i j : Fin n) : ℝ :=
    (m [i,j,j,i]-m [i,j,i,j]-m [j,i,j,i]+m [j,i,i,j]).re
 theorem univariateMoment_continuous (q : Polynomial ℝ) (i : Fin n) : Continuous (fun m : List (Fin n) → ℂ => univariateMoment m q i) := by
  unfold univariateMoment
  fun_prop
 theorem commutatorMoment_continuous (i j : Fin n) : Continuous (fun m : List (Fin n) → ℂ => commutatorMoment m i j) := by
  unfold commutatorMoment
  fun_prop
 theorem univariateMoment_matrix (q : Polynomial ℝ) (a : MatrixCoordinates n d) (i : Fin n) :
    univariateMoment (matrixMoment a) q i=(d:ℝ)⁻¹*∑j,q.eval ((hermitianMatrix_isHermitian a i).eigenvalues j) :=
  matrixUnivariateMoment_eigenvalues q a i
 theorem commutatorMoment_matrix (a : MatrixCoordinates n d) (i j : Fin n) :
    commutatorMoment (matrixMoment a) i j = (d:ℝ)⁻¹*hsNorm (hermitianMatrix a j*hermitianMatrix a i-hermitianMatrix a i*hermitianMatrix a j)^2 := by
  let A := hermitianMatrix a i
  let B := hermitianMatrix a j
  have hA : A.conjTranspose=A := (hermitianMatrix_isHermitian a i).eq
  have hB : B.conjTranspose=B := (hermitianMatrix_isHermitian a j).eq
  rw [hsNorm_sq,← trace_conjTranspose_mul_re]
  change _ = (d:ℝ)⁻¹*(Matrix.trace ((B*A-A*B).conjTranspose*(B*A-A*B))).re
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_mul,hA,hB]
  have he : (A*B-B*A)*(B*A-A*B)=A*B*B*A-A*B*A*B-B*A*B*A+B*A*A*B := by noncomm_ring
  rw [he,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_sub]
  unfold commutatorMoment matrixMoment
  simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  change ((d:ℂ)⁻¹*Matrix.trace (A*(B*(B*A)))-(d:ℂ)⁻¹*Matrix.trace (A*(B*(A*B)))-
    (d:ℂ)⁻¹*Matrix.trace (B*(A*(B*A)))+(d:ℂ)⁻¹*Matrix.trace (B*(A*(A*B)))).re = _
  simp only [← mul_add,← mul_sub,mul_assoc,← Complex.ofReal_natCast,← Complex.ofReal_inv,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
 theorem matrixMoment_second_hs (a : MatrixCoordinates n d) (i : Fin n) :
    (matrixMoment a [i,i]).re=(d:ℝ)⁻¹*hsNorm (hermitianMatrix a i)^2 := by
  rw [hsNorm_sq,← trace_conjTranspose_mul_re,(hermitianMatrix_isHermitian a i).eq]
  simp [matrixMoment,← Complex.ofReal_natCast,← Complex.ofReal_inv]
 theorem matrixMoment_fourth_trace (a : MatrixCoordinates n d) (i : Fin n) :
    (matrixMoment a [i,i,i,i]).re=(d:ℝ)⁻¹*(Matrix.trace (hermitianMatrix a i^4)).re := by
  have he := matrixMoment_replicate a i 4
  simp only [List.replicate_succ,List.replicate_zero] at he
  rw [he]
  simp [← Complex.ofReal_natCast,← Complex.ofReal_inv]
 section Operators
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M)
 theorem continuous_tuple_wordMoments : Continuous (fun X : Fin n → H →L[ℂ] H => wordMoment τ X) := by
  apply continuous_pi
  intro w
  unfold wordMoment trace wordEval
  fun_prop
 theorem univariateMoment_word (X : Fin n → H →L[ℂ] H) (q : Polynomial ℝ) (i : Fin n) :
    univariateMoment (wordMoment τ X) q i=∑k∈q.support,q.coeff k*(trace τ (X i^k)).re := by
  simp [univariateMoment,wordMoment,wordEval]
 theorem commutatorMoment_word_zero (X : Fin n → H →L[ℂ] H) (i j : Fin n) (hc : Commute (X i) (X j)) :
    commutatorMoment (wordMoment τ X) i j=0 := by
  have h1 : X i*(X j*(X j*X i))=X i*(X j*(X i*X j)) := by rw [hc.eq.symm]
  have h2 : X j*(X i*(X j*X i))=X j*(X i*(X i*X j)) := by rw [hc.eq.symm]
  simp only [commutatorMoment,wordMoment,wordEval,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,h1,h2,sub_self,zero_sub,neg_add_cancel,Complex.zero_re]
end Operators
namespace Model
variable (p : ℕ) [NeZero p]
 theorem continuous_X : Continuous (X p) := by
  apply continuous_pi
  intro i
  unfold X heatTuple
  fun_prop
 theorem continuous_X_moments : Continuous (fun h : ℝ => wordMoment (τ p) (X p h)) :=
  (continuous_tuple_wordMoments (τ p)).comp (continuous_X p)
 theorem X_zero : X p 0=C p := by ext i; simp [X,heatTuple]
 theorem C_second (i : Fin p) : (wordMoment (τ p) (C p) [i.castSucc,i.castSucc]).re=1 := by
  have he := FreeTensor.trace_semicircularB_pow (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)) i 2
  simpa [wordMoment,wordEval,pow_two,C_castSucc] using congrArg Complex.re he
 theorem C_fourth (i : Fin p) : (wordMoment (τ p) (C p) [i.castSucc,i.castSucc,i.castSucc,i.castSucc]).re=2 := by
  have he := FreeTensor.trace_semicircularB_pow (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)) i 4
  simpa [wordMoment,wordEval,pow_succ,mul_assoc,C_castSucc,catalan,show Even (4:ℕ) from ⟨2,by norm_num⟩] using congrArg Complex.re he
 theorem C_commutator (i : Fin p) : commutatorMoment (wordMoment (τ p) (C p)) i.castSucc (Fin.last p)=0 := by
  apply commutatorMoment_word_zero
  rw [C_castSucc,C_last]
  exact (FreeTensor.equidiscreteSignal_commutes_B p i).symm
 theorem C_univariateMoment (q : Polynomial ℝ) :
    univariateMoment (wordMoment (τ p) (C p)) q (Fin.last p)=(p:ℝ)⁻¹*∑l : Fin p,q.eval (equidiscreteAtom p l) := by
  rw [univariateMoment_word]
  simp only [C_last,FreeTensor.equidiscreteSignal_moments,← Complex.ofReal_pow,← Complex.ofReal_sum,
    ← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_mul,Complex.ofReal_re]
  simp only [mul_left_comm (q.coeff _),← mul_sum]
  congr 1
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  rw [sum_comm]
  simp only [mul_sum]
end Model
end FiniteEntropySeparation

end

end OAI
