import OAI.NumberTheory.JointDickman.Counting.CountingCutoffError
import OAI.NumberTheory.JointDickman.Probability.CutNormTriangle

namespace OAI

/-! # A cut-norm error from the weights of the candidate representations -/
namespace JointDickman
open Finset

theorem candidateMatrix_abs_le {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (i k : κ) :
    |candidateMatrix row col v i k| ≤ candidateMatrix row col (fun e => |v e|) i k := by
  unfold candidateMatrix
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro e _
  split_ifs <;> simp_all
  exact abs_add_le _ _

theorem candidateMatrix_cutNorm_sub {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v w : ι → ℝ) :
    kernelCutNorm (fun i k => candidateMatrix row col v i k-candidateMatrix row col w i k) ≤
      (2*∑ e, |v e-w e|)/(Fintype.card κ : ℝ) := by
  apply (kernelCutNorm_le_absolute_mass _).trans
  unfold kernelAbsoluteMass
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp_rw [← candidateMatrix_sub]
  calc
    _ ≤ ∑ i, ∑ k, candidateMatrix row col (fun e => |v e-w e|) i k :=
      sum_le_sum (fun i _ => sum_le_sum (fun k _ => candidateMatrix_abs_le row col _ i k))
    _ = _ := candidateMatrix_total row col _

theorem latentCandidateKernel_cutNorm_sub (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ ψ : BlockCandidateIndex M → ℝ) :
    kernelCutNorm (fun i k => latentCandidateKernel B L T H M τ C S χ i k-
      latentCandidateKernel B L T H M τ C S ψ i k) ≤
        (2*∑ e : blockCandidates B L T H M τ C S,
          |candidateMeanWeight B L τ C S χ e.val-candidateMeanWeight B L τ C S ψ e.val|)/(M : ℝ) := by
  unfold latentCandidateKernel
  simpa only [Fintype.card_fin] using candidateMatrix_cutNorm_sub
    (fun e : blockCandidates B L T H M τ C S => e.val.1.1) (fun e => e.val.1.2)
    (fun e => candidateMeanWeight B L τ C S χ e.val) (fun e => candidateMeanWeight B L τ C S ψ e.val)

end JointDickman

end OAI
