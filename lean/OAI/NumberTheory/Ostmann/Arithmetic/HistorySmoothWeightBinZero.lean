import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCutoffDeriv
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightStateDeriv

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicState.StateExpr
open Construction Characters.RationalHistory HistorySymbolicEncoding
open scoped ContDiff FourierTransform SchwartzMap
variable {ι : Type*} [DecidableEq ι] {a : State}

theorem realScalar_logCurve_deriv_zero_of_bins_zero (e : StateExpr a ι) (b s : ℕ)
    (X tb td : ℝ) (outside : List ℕ) (x : ι → ℝ) (i : ι)
    (hX : 0 < X) (hx : ∀ j, 0 < x j) (houtside : ∀ q ∈ outside, 0 < q)
    (hP : 0 < e.realPeriod outside x)
    (he : (e.periodExpr outside).RealRegularAt x) (hatoms : StateSmallAtoms e)
    (hzero : realStateBins b s tb td a outside (fun j => (e.small j).realEval x)
      (fun j => (outside.get j:ℝ)) = 0) :
    deriv (fun t => e.realScalar b s X tb td outside (Expr.logCurve x i t)) 0 = 0 := by
  choose q hq using hatoms
  let P := e.periodExpr outside
  let ρ : 𝓢(ℝ,ℂ) := 𝓕 SchwartzCutoff.psi
  let F (t : ℝ) := exprLeafScalar ρ (a.frequency:ℝ) X P (Expr.logCurve x i t)
  let B (t : ℝ) := realStateBins b s tb td a outside
    (fun j => Expr.logCurve x i t (q j)) (fun j => (outside.get j:ℝ))
  have hc := P.hasDerivAt_logCurve x i he
  have hp0 : P.realEval (Expr.logCurve x i 0) ≠ 0 := by
    simpa only [Expr.logCurve_zero,P,periodExpr_realEval] using hP.ne'
  have hratio := ((differentiableAt_const X).div hc.differentiableAt hp0 :
    DifferentiableAt ℝ (fun t => X / P.realEval (Expr.logCurve x i t)) 0)
  have hsqrt := hratio.sqrt (div_ne_zero hX.ne' hp0)
  have harg := ((differentiableAt_const (-(a.frequency:ℝ) * X)).div hc.differentiableAt hp0 :
    DifferentiableAt ℝ (fun t => -(a.frequency:ℝ) * X / P.realEval (Expr.logCurve x i t)) 0)
  have hF : DifferentiableAt ℝ F 0 :=
    (Complex.ofRealCLM.differentiableAt.comp 0 hsqrt).mul (ρ.differentiableAt.comp 0 harg)
  have hBcd := realStateBins_contDiffAt b s tb td a outside
    (fun t j => Expr.logCurve x i t (q j)) (fun (_ : ℝ) j => (outside.get j:ℝ)) 0
    (fun j => by unfold Expr.logCurve; split_ifs <;> fun_prop)
    (fun j => contDiffAt_const)
    (fun j => by simpa only [Expr.logCurve_zero] using hx (q j))
    (fun j => by exact_mod_cast houtside (outside.get j) (List.get_mem outside j))
  have hB : DifferentiableAt ℝ B 0 := hBcd.differentiableAt (by simp)
  have hBc : DifferentiableAt ℝ (fun t => (B t:ℂ)) 0 := Complex.ofRealCLM.differentiableAt.comp 0 hB
  have heq : (fun t => e.realScalar b s X tb td outside (Expr.logCurve x i t)) =
      (fun t => F t * (B t:ℂ)) := by
    funext t
    unfold realScalar F exprLeafScalar B
    simp only [P,periodExpr_realEval,ρ]
    congr 2
    apply congrArg (fun y => realStateBins b s tb td a outside y (fun j => (outside.get j:ℝ)))
    funext j
    rw [hq j]
    rfl
  have hB0 : B 0 = 0 := by
    convert hzero using 1
    dsimp only [B]
    rw [Expr.logCurve_zero]
    congr 1
    funext j
    rw [hq j]
    rfl
  have hdB : deriv B 0 = 0 :=
    deriv_eq_zero_of_nonneg_of_eq_zero B 0 (fun t => (realStateBins_bounds _ _ _ _ _ _ _ _).1) hB0
  rw [heq,deriv_fun_mul hF hBc,hB.hasDerivAt.ofReal_comp.deriv,hdB,hB0]
  simp only [Complex.ofReal_zero,mul_zero,add_zero]

end Ostmann.Arithmetic.HistorySymbolicState.StateExpr

end

end OAI
