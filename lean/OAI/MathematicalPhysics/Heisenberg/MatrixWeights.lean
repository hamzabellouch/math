import OAI.MathematicalPhysics.Heisenberg.FiniteTilt

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.Selection
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma exp_diagonal_pos (A : Matrix I I ℝ) (hA : A.transpose=A) (i : I) :
    0<NormedSpace.exp A i i := by
  let B:=NormedSpace.exp ((1/2:ℝ) • A)
  have hB : B.transpose=B := by
    dsimp only [B]
    rw [←Matrix.exp_transpose,Matrix.transpose_smul,hA]
  have hsq : NormedSpace.exp A=B*B.transpose := by
    rw [hB]
    dsimp only [B]
    rw [←Matrix.exp_add_of_commute _ _ (Commute.refl _)]
    congr 1
    module
  have hinv : B*NormedSpace.exp (-((1/2:ℝ) • A))=1 := by
    dsimp only [B]
    rw [←Matrix.exp_add_of_commute _ _ (Commute.refl ((1/2:ℝ) • A)).neg_right,add_neg_cancel,NormedSpace.exp_zero]
  have hn : ∃ j,B i j≠0 := by
    by_contra hh
    push Not at hh
    have he:=congrArg (fun M : Matrix I I ℝ=>M i i) hinv
    norm_num only [Matrix.mul_apply,hh,zero_mul,Finset.sum_const_zero,Matrix.one_apply_eq] at he
  rw [hsq,Matrix.mul_apply]
  apply Finset.sum_pos'
  · intro j _; change 0≤B i j*B i j; exact mul_self_nonneg _
  · obtain ⟨j,hj⟩:=hn
    exact ⟨j,Finset.mem_univ _,mul_self_pos.mpr hj⟩

lemma exp_trace_pos [Nonempty I] (A : Matrix I I ℝ) (hA : A.transpose=A) :
    0<Matrix.trace (NormedSpace.exp A) :=
  Finset.sum_pos (fun i _=>exp_diagonal_pos A hA i) Finset.univ_nonempty

lemma exp_tilt (A : Matrix I I ℝ) (m : I → ℝ) (b : ℝ)
    (hcomm : Commute A (Matrix.diagonal m)) :
    NormedSpace.exp (A+b • Matrix.diagonal m)=
      NormedSpace.exp A*Matrix.diagonal (fun i=>Real.exp (b*m i)) := by
  rw [Matrix.exp_add_of_commute _ _ (hcomm.smul_right b)]
  congr 1
  rw [←Matrix.diagonal_smul,Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp]
  rw [Real.exp_eq_exp_ℝ]
  rfl

lemma trace_exp_tilt (A : Matrix I I ℝ) (m : I → ℝ) (b : ℝ)
    (hcomm : Commute A (Matrix.diagonal m)) :
    Matrix.trace (NormedSpace.exp (A+b • Matrix.diagonal m))=
      tiltPartition (fun i=>NormedSpace.exp A i i) m b := by
  rw [exp_tilt A m b hcomm]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,tiltPartition]

lemma trace_exp_tilt_mag (A : Matrix I I ℝ) (m : I → ℝ) (b : ℝ)
    (hcomm : Commute A (Matrix.diagonal m)) :
    Matrix.trace (NormedSpace.exp (A+b • Matrix.diagonal m)*Matrix.diagonal m)=
      ∑ i,NormedSpace.exp A i i*Real.exp (b*m i)*m i := by
  rw [exp_tilt A m b hcomm]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal]

lemma trace_spectral_tail (E : Matrix I I ℝ) (m : I → ℝ) (a : ℝ) :
    Matrix.trace (E*Matrix.diagonal (fun i=>if a≤ m i then (1:ℝ) else 0))=
      weightedTail (fun i=>E i i) m a := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,weightedTail,mul_ite,mul_one,mul_zero]

end Heisenberg.Selection
end
end

end OAI
