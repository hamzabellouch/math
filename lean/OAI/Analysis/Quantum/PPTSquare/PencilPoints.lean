import OAI.Analysis.Quantum.PPTSquare.PencilGeometry

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open Matrix Polynomial PencilAlgebra PencilEvaluation PencilGeometry
namespace PencilPoints
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
lemma coordinates (t : Fin 3 → K) (a : Fin 3) :
    lowMon t (![3,2,1] a) = t a := by
  fin_cases a <;> simp [lowMon, lowExp, Fin.prod_univ_succ]
omit [CharZero K] in
lemma lowMon_injective : Function.Injective (lowMon (K := K)) := by
  intro s t h
  ext a
  simpa only [coordinates] using congrFun h (![3,2,1] a)

omit [CharZero K] in
lemma eigen_index (A : Matrix (Fin 20) (Fin 20) K) (r : Fin 20 → K)
    (hf : A.charpoly = ∏ i, (X - C (r i))) (z : Fin 20 → K) (hz : z ≠ 0)
    (μ : K) (he : z ᵥ* A = μ • z) : ∃ i, μ = r i := by
  have hv : Module.End.HasEigenvector A.transpose.toLin' μ z := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_,hz⟩
    ext j
    have hh := congrFun he j
    simpa only [Matrix.toLin'_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hh
  have hh := (Module.End.hasEigenvalue_iff_isRoot_charpoly A.transpose.toLin' μ).mp (Module.End.hasEigenvalue_of_hasEigenvector hv)
  rw [Matrix.charpoly_toLin', Matrix.charpoly_transpose, hf] at hh
  simpa only [IsRoot.def, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero] using hh

lemma affine_points (r : Fin 20 → K) (hr : Function.Injective r)
    (hf : (action (K := K) 0).charpoly = ∏ i, (X - C (r i)))
    (t : Fin 20 → Fin 3 → K) (hu : IsUnit (evaluation t))
    (he : ∀ a, evaluation t * action a = diagonal (fun i => (denominator : K)*t i a) * evaluation t)
    (ht : ∀ i, (denominator : K)*t i 0 = r i) :
    Function.Injective t ∧ (∀ i, minors ![1,t i 0,t i 1,t i 2] = 0) ∧
      (∀ s : Fin 3 → K, minors ![1,s 0,s 1,s 2] = 0 ↔ ∃ i, s = t i) := by
  have hit : Function.Injective t := by
    intro i j hh
    apply hr
    rw [← ht i, ← ht j, hh]
  have hep : evaluation t * action 0 = diagonal r * evaluation t := by
    convert he 0 using 1
    congr 2
    ext i
    exact (ht i).symm
  have hrow (i : Fin 20) (a : Fin 3) : lowMon (t i) ᵥ* action a =
      ((denominator : K)*t i a) • lowMon (t i) := by
    ext j
    have hh := congrFun (congrFun (he a) i) j
    rw [Matrix.diagonal_mul] at hh
    exact hh
  have hm (i : Fin 20) : minors ![1,t i 0,t i 1,t i 2] = 0 :=
    minors_of_eigen (t i) (hrow i)
  refine ⟨hit,hm,?_⟩
  intro s
  constructor
  · intro hs
    have hz : lowMon s ≠ 0 := by
      intro h
      have hh := congrFun h 0
      exact one_ne_zero (by simpa only [lowMon_zero, Pi.zero_apply] using hh)
    obtain ⟨i,hi⟩ := eigen_index (action 0) r hf (lowMon s) hz ((denominator : K)*s 0)
      (eigen_of_minors s hs 0)
    refine ⟨i,lowMon_injective ?_⟩
    have hh : lowMon s ᵥ* action 0 = r i • lowMon s := by rw [← hi]; exact eigen_of_minors s hs 0
    exact EigenRows.normalized_row_unique (evaluation t) (action 0) r hr hu hep 0
      (fun j => lowMon_zero (t j)) i (lowMon s) hh (lowMon_zero s)
  · rintro ⟨i,rfl⟩
    exact hm i

omit [CharZero K] in
lemma pencil_smul (c : K) (x : Fin 4 → K) : pencil (c • x) = c • pencil x := by
  simp only [pencil, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
omit [CharZero K] in
lemma rank_smul (c : K) (hc : c ≠ 0) (x : Fin 4 → K) : (pencil (c • x)).rank = (pencil x).rank := by
  rw [pencil_smul]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc)

lemma no_infinity (x : Fin 4 → K) (hx : x ≠ 0) (hr : (pencil x).rank < 4) : x 0 ≠ 0 := by
  intro hz
  have he : x = ![0,x 1,x 2,x 3] := by ext a; fin_cases a <;> simp [hz]
  have hm := (rank_lt_iff x).mp hr
  rw [he] at hm
  have ht := infinity_zero ![x 1,x 2,x 3] (by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] using
      hm)
  apply hx
  ext a
  fin_cases a
  · exact hz
  · exact congrFun ht 0
  · exact congrFun ht 1
  · exact congrFun ht 2

end PencilPoints

end

end OAI
