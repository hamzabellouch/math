import OAI.Combinatorics.ThinTrees.IndependentVectors

namespace OAI

universe uD

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {D : Type uD} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
lemma rankOne_smul (c : ℝ) (v : D → ℝ) :
    Matrix.vecMulVec (c • v) (c • v)=c^2 • Matrix.vecMulVec v v := by
  apply Matrix.ext
  intro a b
  simp [Matrix.vecMulVec,Matrix.smul_apply,Pi.smul_apply]
  ring

omit [DecidableEq D] in
lemma sum_column_rankOne (M : Matrix D D ℝ) :
    ∑d, Matrix.vecMulVec (fun a => M a d) (fun a => M a d)=M*Mᵀ := by
  apply Matrix.ext
  intro a b
  simp [Matrix.sum_apply,Matrix.mul_apply,Matrix.vecMulVec,Matrix.transpose_apply]

omit [DecidableEq D] in
lemma rankOne_trace_nonneg (v : D → ℝ) : 0 ≤ (Matrix.vecMulVec v v).trace := by
  exact (rankOne_posSemidef v).trace_nonneg

lemma deterministic_padding (R : Matrix D D ℝ) (hR : R.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ∃N : ℕ, ∃u : Fin N × D → D → ℝ,
      (∑p, Matrix.vecMulVec (u p) (u p))=R ∧
      ∀p, (Matrix.vecMulVec (u p) (u p)).trace ≤ ε := by
  let S := CFC.sqrt R
  have hS : S.IsHermitian := (CFC.sqrt_nonneg R).posSemidef.isHermitian
  have hsum : (∑d, Matrix.vecMulVec (fun a => S a d) (fun a => S a d))=R := by
    rw [sum_column_rankOne]
    have ht : Sᵀ=S := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.eq
    rw [ht]
    exact CFC.sqrt_mul_sqrt_self R hR.nonneg
  have htr : ∀d, (Matrix.vecMulVec (fun a => S a d) (fun a => S a d)).trace ≤ R.trace := by
    intro d
    rw [←hsum,Matrix.trace_sum]
    exact Finset.single_le_sum (fun e _ => rankOne_trace_nonneg (fun a => S a e)) (Finset.mem_univ d)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (R.trace/ε))
  have hNpos : 0 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNε : R.trace/(N : ℝ) ≤ ε := by
    have hh : R.trace/ε ≤ N := (le_max_right _ _).trans hN.le
    apply (div_le_iff₀ hNpos).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hh
  let c : ℝ := Real.sqrt (1/(N : ℝ))
  have hc : c^2=1/(N : ℝ) := Real.sq_sqrt (by positivity)
  let u : Fin N × D → D → ℝ := fun p => c • (fun a => S a p.2)
  refine ⟨N,u,?_,?_⟩
  · simp only [u,rankOne_smul,hc,Fintype.sum_prod_type,←Finset.smul_sum,hsum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
    rw [←Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hNpos.ne']
  · intro p
    simp only [u,rankOne_smul,hc,Matrix.trace_smul,smul_eq_mul]
    calc
      (1/(N : ℝ)) * (Matrix.vecMulVec (fun a => S a p.2) (fun a => S a p.2)).trace
          ≤ (1/(N : ℝ))*R.trace := mul_le_mul_of_nonneg_left (htr p.2) (by positivity)
      _ = R.trace/(N : ℝ) := by ring
      _ ≤ ε := hNε

end StrongThinTree.MSS

end
end

end OAI
