import OAI.Analysis.FreeEntropy.HeatCumulants

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
open FreeSeries
 theorem reparam_matrixTraceWord {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {d : ℕ}
    (X : α → Matrix (Fin d) (Fin d) ℂ) (c : α → β → ℂ) :
    reparam c (matrixTraceWord X) = matrixTraceWord (fun b => ∑ a, c a b • X a) := by
  let Y := fun b => ∑ a, c a b • X a
  have hh (w : List β) (A : Matrix (Fin d) (Fin d) ℂ) :
      reparam c (fun v => (d:ℂ)⁻¹*Matrix.trace (A * matrixWord X v)) w = (d:ℂ)⁻¹*Matrix.trace (A * matrixWord Y w) := by
    induction w generalizing A with
    | nil => simp [matrixWord]
    | cons b w ih =>
      rw [reparam_cons]
      have hf (a : α) : deriv a (fun v => (d:ℂ)⁻¹*Matrix.trace (A * matrixWord X v)) =
          (fun v => (d:ℂ)⁻¹*Matrix.trace ((A * X a) * matrixWord X v)) := by
        funext v; simp [FreeSeries.deriv, matrixWord, mul_assoc]
      simp only [hf, ih]
      change _ = (d:ℂ)⁻¹*Matrix.trace (A * (Y b * matrixWord Y w))
      rw [← mul_assoc]
      dsimp only [Y]
      rw [Finset.mul_sum, Finset.sum_mul, Matrix.trace_sum,Finset.mul_sum]
      apply sum_congr rfl
      intro a _
      simp only [mul_smul_comm, smul_mul_assoc, Matrix.trace_smul,smul_eq_mul]
      ring
  funext w
  change reparam c (fun v => (d:ℂ)⁻¹*Matrix.trace (matrixWord X v)) w = _
  simpa only [one_mul,Y,matrixTraceWord] using hh w 1
 def jointFinMatrix {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (x : MatrixIndex n d → ℝ) : Fin (n+n) → Matrix (Fin d) (Fin d) ℂ :=
  Fin.addCases A (gueMatrix x)
 theorem jointFinMatrix_trace {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (x : MatrixIndex n d → ℝ) (w : List (Fin (n+n))) :
    matrixTraceWord (jointFinMatrix A x) w = matrixTraceWord (jointMatrix A x) (w.map finSumFinEquiv.symm) := by
  rw [matrixTraceWord_map]
  congr 1
  funext j
  obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective j
  cases a with
  | inl i => simp only [Function.comp_apply,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_apply_left,jointFinMatrix,Fin.addCases_left,jointMatrix,Sum.elim_inl]
  | inr i => simp only [Function.comp_apply,finSumFinEquiv_symm_apply_natAdd,finSumFinEquiv_apply_right,jointFinMatrix,Fin.addCases_right,jointMatrix,Sum.elim_inr]
 def heatMatrix {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (u : ℝ) (x : MatrixIndex n d → ℝ) : Fin n → Matrix (Fin d) (Fin d) ℂ :=
  fun i => A i+(Real.sqrt u:ℂ) • gueMatrix x i
 theorem heatMatrix_linear {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (u : ℝ) (x : MatrixIndex n d → ℝ) :
    (fun i => ∑ j, heatCoefficients u j i • jointFinMatrix A x j)=heatMatrix A u x := by
  funext i
  rw [Fin.sum_univ_add]
  simp only [jointFinMatrix,Fin.addCases_left,Fin.addCases_right]
  change (∑ j:Fin n,heatCoefficients u (leftIndex j) i • A j)+
    (∑ j:Fin n,heatCoefficients u (rightIndex j) i • gueMatrix x j)=_
  simp [heatMatrix,ite_smul]
end FiniteEntropySeparation

end

end OAI
