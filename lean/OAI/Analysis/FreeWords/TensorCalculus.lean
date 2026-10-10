import Mathlib

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators Matrix.Norms.L2Operator

open NormedSpace

noncomputable section

def tensorMatrix {r d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ :=
  fun a b => ∏ i, U (a i) (b i)

def lieMatrix {r d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ :=
  fun a b => ∑ s, (∏ t ∈ Finset.univ.erase s, if a t=b t then (1 : ℂ) else 0)*A (a s) (b s)

theorem lieMatrix_add {r d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    lieMatrix (r := r) (A+B)=lieMatrix A+lieMatrix B := by
  ext a b
  simp [lieMatrix,mul_add,Finset.sum_add_distrib]

theorem lieMatrix_smul {r d : ℕ} (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    lieMatrix (r := r) (c • A)=c • lieMatrix A := by
  ext a b
  simp [lieMatrix,Finset.mul_sum,mul_left_comm]

theorem lieMatrix_sub {r d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    lieMatrix (r := r) (A-B)=lieMatrix A-lieMatrix B := by
  ext a b
  simp [lieMatrix,mul_sub,Finset.sum_sub_distrib]

def matrixEntryCLM {d : ℕ} (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem matrixEntryCLM_apply {d : ℕ} (i j : Fin d) (A : Matrix (Fin d) (Fin d) ℂ) :
    matrixEntryCLM i j A=A i j := rfl

theorem hasDerivAt_tensor_exp {r d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin r → Fin d) :
    HasDerivAt (fun t : ℝ => tensorMatrix (exp (t • A)) a b) (lieMatrix A a b) 0 := by
  have he : HasDerivAt (fun t : ℝ => exp (t • A)) A 0 := by
    simpa using hasDerivAt_exp_smul_const A (0 : ℝ)
  have hel (i j : Fin d) : HasDerivAt (fun t : ℝ => (exp (t • A)) i j) (A i j) 0 := by
    simpa only [Function.comp_def,matrixEntryCLM_apply] using (matrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt 0 he
  have hp := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun s _ => hel (a s) (b s))
  simpa [tensorMatrix,lieMatrix,Matrix.one_apply,smul_eq_mul] using hp

theorem commute_lieMatrix_skew {r d : ℕ}
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      Commute T (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)))
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : star A= -A) : Commute T (lieMatrix A) := by
  let _ : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := .restrictScalars ℚ ℂ _
  ext a b
  have hp (t : ℝ) : exp (t • A) ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
    apply exp_mem_unitary_of_mem_skewAdjoint
    change star (t • A)= -(t • A)
    simp [hA]
  have heq (t : ℝ) :
      (∑ c, T a c*tensorMatrix (exp (t • A)) c b)=
      ∑ c, tensorMatrix (exp (t • A)) a c*T c b := by
    exact congrFun (congrFun (hT ⟨exp (t • A),hp t⟩).eq a) b
  have hL : HasDerivAt (fun t : ℝ => ∑ c, T a c*tensorMatrix (exp (t • A)) c b)
      (∑ c, T a c*lieMatrix A c b) 0 := by
    exact HasDerivAt.fun_sum (fun c _ => (hasDerivAt_tensor_exp A c b).const_mul (T a c))
  have hR : HasDerivAt (fun t : ℝ => ∑ c, tensorMatrix (exp (t • A)) a c*T c b)
      (∑ c, lieMatrix A a c*T c b) 0 := by
    exact HasDerivAt.fun_sum (fun c _ => (hasDerivAt_tensor_exp A a c).mul_const (T c b))
  exact hL.unique (hR.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => heq t)))

theorem commute_lieMatrix {r d : ℕ}
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      Commute T (tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ)))
    (A : Matrix (Fin d) (Fin d) ℂ) : Commute T (lieMatrix A) := by
  have h1 : star (A-star A)= -(A-star A) := by simp [star_sub]
  have h2 : star (Complex.I • (A+star A))= -(Complex.I • (A+star A)) := by
    simp [star_smul,star_add,Complex.conj_I,add_comm]
  have hc1 := commute_lieMatrix_skew T hT (A-star A) h1
  have hc2 := commute_lieMatrix_skew T hT (Complex.I • (A+star A)) h2
  have he : A=(1/2 : ℂ) • ((A-star A)-Complex.I • (Complex.I • (A+star A))) := by
    simp only [smul_smul,Complex.I_mul_I,neg_one_smul,sub_neg_eq_add]
    module
  rw [he,lieMatrix_smul,lieMatrix_sub,lieMatrix_smul]
  exact (hc1.sub_right (hc2.smul_right Complex.I)).smul_right (1/2 : ℂ)

end

end KKWeingarten
end

end OAI
