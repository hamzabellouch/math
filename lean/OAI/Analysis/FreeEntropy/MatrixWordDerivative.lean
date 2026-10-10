import OAI.Analysis.FreeEntropy.MatrixOperator

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 variable {α : Type u1} {d : ℕ}
 def matrixWord (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) : Matrix (Fin d) (Fin d) ℂ := (w.map A).prod
 @[simp] theorem matrixWord_nil (A : α → Matrix (Fin d) (Fin d) ℂ) : matrixWord A [] = 1 := rfl
 @[simp] theorem matrixWord_cons (A : α → Matrix (Fin d) (Fin d) ℂ) (a : α) (w : List α) : matrixWord A (a::w) = A a*matrixWord A w := rfl
 theorem matrixWord_append (A : α → Matrix (Fin d) (Fin d) ℂ) (u v : List α) : matrixWord A (u++v) = matrixWord A u*matrixWord A v := by simp [matrixWord]
 def matrixWordVariation (A D : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) : Matrix (Fin d) (Fin d) ℂ :=
   ∑ r : Fin w.length, matrixWord A (w.take r.val) * D w[r.val] * matrixWord A (w.drop (r.val+1))
 @[simp] theorem matrixWordVariation_nil (A D : α → Matrix (Fin d) (Fin d) ℂ) : matrixWordVariation A D [] = 0 := by simp [matrixWordVariation]
 theorem matrixWordVariation_cons (A D : α → Matrix (Fin d) (Fin d) ℂ) (a : α) (w : List α) :
    matrixWordVariation A D (a::w) = D a*matrixWord A w + A a*matrixWordVariation A D w := by
  unfold matrixWordVariation
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, List.take_zero, matrixWord_nil, Nat.zero_add, List.getElem_cons_zero, one_mul,
    Fin.val_succ, List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons, matrixWord_cons]
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro r _
  simp [mul_assoc]
 theorem hasDerivAt_matrixWord {A : ℝ → α → Matrix (Fin d) (Fin d) ℂ} {D : α → Matrix (Fin d) (Fin d) ℂ} {t : ℝ}
    (hA : ∀ a j k, HasDerivAt (fun s => A s a j k) (D a j k) t) (w : List α) :
    ∀ j k, HasDerivAt (fun s => matrixWord (A s) w j k) (matrixWordVariation (A t) D w j k) t := by
  induction w with
  | nil => intro j k; simpa using hasDerivAt_const t ((1 : Matrix (Fin d) (Fin d) ℂ) j k)
  | cons a w ih =>
    rw [matrixWordVariation_cons]
    exact hasDerivAt_matrix_mul (hA a) ih
 theorem hasDerivAt_matrixWord_trace {A : ℝ → α → Matrix (Fin d) (Fin d) ℂ} {D : α → Matrix (Fin d) (Fin d) ℂ} {t : ℝ}
    (hA : ∀ a j k, HasDerivAt (fun s => A s a j k) (D a j k) t) (w : List α) :
    HasDerivAt (fun s => Matrix.trace (matrixWord (A s) w)) (Matrix.trace (matrixWordVariation (A t) D w)) t := by
  simpa only [Matrix.trace, Matrix.diag, Finset.sum_fn] using HasDerivAt.sum (u := univ) (fun j _ => hasDerivAt_matrixWord hA w j j)
 theorem matrixWordVariation_trace (A D : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) :
    Matrix.trace (matrixWordVariation A D w) = ∑ r : Fin w.length,
      Matrix.trace (D w[r.val] * (matrixWord A (w.drop (r.val+1))*matrixWord A (w.take r.val))) := by
  rw [matrixWordVariation, Matrix.trace_sum]
  apply sum_congr rfl
  intro r _
  rw [Matrix.trace_mul_cycle]
  exact Matrix.trace_mul_comm _ _
 def cyclicMatrixWord (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) (r : Fin w.length) : Matrix (Fin d) (Fin d) ℂ :=
   matrixWord A (w.drop (r.val+1))*matrixWord A (w.take r.val)
 theorem cyclicMatrixWord_bound (A : α → Matrix (Fin d) (Fin d) ℂ) (w : List α) (r : Fin w.length)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ i ∈ w, matrixOpNorm (A i) ≤ K) :
    matrixOpNorm (cyclicMatrixWord A w r) ≤ K^(w.length-1) := by
  rw [cyclicMatrixWord, ← matrixWord_append]
  have hb := matrixOpNorm_word A (w.drop (r.val+1)++w.take r.val) hK (by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hA i (List.mem_of_mem_drop hi)
    · exact hA i (List.mem_of_mem_take hi))
  have he : (w.drop (r.val+1)++w.take r.val).length = w.length-1 := by
    simp only [List.length_append, List.length_drop, List.length_take]
    have hr := r.isLt
    omega
  simpa only [he, matrixWord] using hb
end FiniteEntropySeparation

end

end OAI
