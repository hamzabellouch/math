import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightBinsDeriv
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExprFourier
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPeriod

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicState.StateExpr
open Construction Characters.RationalHistory HistorySymbolicEncoding
open scoped ContDiff FourierTransform SchwartzMap
variable {ι : Type*} [DecidableEq ι] {a : State}

theorem realScalar_logCurve_deriv_bound (e : StateExpr a ι) (b s : ℕ) (X tb td : ℝ)
    (outside : List ℕ) (x : ι → ℝ) (i : ι) (K D : ℝ)
    (hX : 0 < X) (hx : ∀ j, 0 < x j) (houtside : ∀ q ∈ outside, 0 < q)
    (hP : 0 < e.realPeriod outside x) (hK : 1 ≤ K)
    (he : (e.periodExpr outside).RelativeControl x K) (hatoms : StateSmallAtoms e)
    (hD : 0 ≤ D) (hφ : ∀ z, |deriv smoothPartition z| ≤ D) :
    ‖deriv (fun t => e.realScalar b s X tb td outside (Expr.logCurve x i t)) 0‖ ≤
      Real.sqrt (X / e.realPeriod outside x) *
        (leafProfileBound (𝓕 SchwartzCutoff.psi) * (e.periodExpr outside).logBudget K +
          leafFourierBound * (2 * D * a.small.length)) := by
  choose q hq using hatoms
  let P := e.periodExpr outside
  let ρ : 𝓢(ℝ,ℂ) := 𝓕 SchwartzCutoff.psi
  let F (t : ℝ) := exprLeafScalar ρ (a.frequency:ℝ) X P (Expr.logCurve x i t)
  let B (t : ℝ) := realStateBins b s tb td a outside
    (fun j => Expr.logCurve x i t (q j)) (fun j => (outside.get j:ℝ))
  have hc := P.hasDerivAt_logCurve x i (Expr.RelativeControl.regular P x K he)
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
  have hdF := exprLeafScalar_logCurve_deriv_bound ρ (a.frequency:ℝ) X P x i K hX hP hK he
  have hdB : ‖deriv (fun t => (B t:ℂ)) 0‖ ≤ 2*D*a.small.length := by
    rw [hB.hasDerivAt.ofReal_comp.deriv,Complex.norm_real,Real.norm_eq_abs]
    exact realStateBins_logCurve_deriv_bound b s tb td a outside q x i D hx hD hφ
  have hnB : ‖(B 0:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (realStateBins_bounds b s tb td a outside _ _).1]
    exact (realStateBins_bounds b s tb td a outside _ _).2
  have hnF : ‖F 0‖ ≤ Real.sqrt (X / e.realPeriod outside x) * leafFourierBound := by
    simp only [F,exprLeafScalar,Expr.logCurve_zero,P,periodExpr_realEval,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_fourier_psi_le _) (Real.sqrt_nonneg _)
  rw [heq,deriv_fun_mul hF hBc]
  calc
    _ ≤ ‖deriv F 0‖ * ‖(B 0:ℂ)‖ + ‖F 0‖ * ‖deriv (fun t => (B t:ℂ)) 0‖ := by
      simpa only [norm_mul] using norm_add_le (deriv F 0 * (B 0:ℂ)) (F 0 * deriv (fun t => (B t:ℂ)) 0)
    _ ≤ (Real.sqrt (X / e.realPeriod outside x) * leafProfileBound ρ * P.logBudget K) * 1 +
        (Real.sqrt (X / e.realPeriod outside x) * leafFourierBound) * (2*D*a.small.length) :=
      add_le_add (mul_le_mul hdF hnB (norm_nonneg _)
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (leafProfileBound_pos ρ).le)
          (Expr.logBudget_nonneg P (zero_le_one.trans hK))))
        (mul_le_mul hnF hdB (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) leafFourierBound_pos.le))
    _ = _ := by dsimp [ρ,P]; ring

end Ostmann.Arithmetic.HistorySymbolicState.StateExpr

end

end OAI
