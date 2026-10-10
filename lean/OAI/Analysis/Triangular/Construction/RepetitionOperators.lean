import OAI.Analysis.Triangular.Construction.BlockOperators
import OAI.Analysis.Triangular.Construction.RepetitionBound

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate
lemma repetitionNorm_nonneg : 0≤repetitionNorm := by
  unfold repetitionNorm
  exact div_nonneg (mul_nonneg (by linarith [pi_eta_pos]) repetitionRatio_pos.le)
    (sub_pos.mpr repetitionRatio_lt).le
abbrev TrigonometricCoefficients := ℓ¹(Fin 22,ℝ)
def AallKernel (p : TailNode × Fin 2) (i : Fin 22) : ℝ :=
  repetitionKernel p ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩
def AallOperator : TrigonometricCoefficients →L[ℝ] TailCoefficients :=
  operator AallKernel (fun _ => (repetitionKernel_bounds _ _).1) repetitionNorm
    (fun _ => (repetitionKernel_bounds _ _).2)
lemma AallOperator_norm : ‖AallOperator‖ ≤ repetitionNorm :=
  operator_norm _ _ _ repetitionNorm_nonneg _
def Akernel (p : TailNode × Fin 2) (i : Fin 20) : ℝ :=
  repetitionKernel p ⟨i.val/2+1,by omega⟩ ⟨i.val%2,by omega⟩
def Aoperator : FiniteCoefficients →L[ℝ] TailCoefficients :=
  operator Akernel (fun _ => (repetitionKernel_bounds _ _).1) repetitionNorm
    (fun _ => (repetitionKernel_bounds _ _).2)
lemma Aoperator_norm : ‖Aoperator‖ ≤ repetitionNorm :=
  operator_norm _ _ _ repetitionNorm_nonneg _
def CallKernel (p : TailNode × Fin 2) (i : Fin 22) : ℝ :=
  jet H h p.1.val.val p.2 (finiteColumn ⟨i.val,by omega⟩)
def CallOperator : TrigonometricCoefficients →L[ℝ] TailCoefficients :=
  operator CallKernel (fun _ => (tail_atom_column_bounds 1 0 _).1) (7/10^15)
    (fun i => (tail_finite_column_bound i).le)
lemma CallOperator_norm : ‖CallOperator‖ ≤ 7/10^15 :=
  operator_norm _ _ _ (by norm_num) _
def beta : ℝ := 3/10^10
def delta : ℝ := 3/10^8
lemma AC_bound : ‖Aoperator‖+‖Coperator‖ ≤ beta := by
  have hA := Aoperator_norm
  have hC := Coperator_norm
  have hr := repetitionNorm_bound
  norm_num [beta] at *
  linarith
lemma AC_all_bound : ‖AallOperator‖+‖CallOperator‖ ≤ beta := by
  have hA := AallOperator_norm
  have hC := CallOperator_norm
  have hr := repetitionNorm_bound
  norm_num [beta] at *
  linarith
end AtomicTriangular.Construction
end

end OAI
