import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightBins
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPivot
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicEncoding
import OAI.NumberTheory.Ostmann.Construction.SmoothHistoryFactor

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicState.StateExpr
open Construction Characters.RationalHistory HistorySymbolicStep
open scoped ContDiff FourierTransform SchwartzMap
variable {ι : Type*} {a : State}

def realPeriod (e : StateExpr a ι) (outside : List ℕ) (x : ι → ℝ) : ℝ :=
  (outsideProduct outside:ℝ) * (e.plus.realEval x *
    (e.minus.realEval x * (product (List.ofFn e.small)).realEval x))

def realScalar (e : StateExpr a ι) (b s : ℕ) (X tb td : ℝ) (outside : List ℕ)
    (x : ι → ℝ) : ℂ :=
  (Real.sqrt (X / e.realPeriod outside x):ℂ) *
    𝓕 SchwartzCutoff.psi (-(a.frequency:ℝ) * X / e.realPeriod outside x) *
    (realStateBins b s tb td a outside (fun i => (e.small i).realEval x)
      (fun i => outside.get i):ℂ)

theorem realPeriod_correct (e : StateExpr a ι) (outside : List ℕ) (x : ι → ℚ)
    (he : e.Correct x) :
    e.realPeriod outside (fun i => (x i:ℝ)) = (outsideProduct outside * a.product:ℕ) := by
  have hp := (HistorySymbolicSlots.product_correct e.small he.2.2.2.2).2
  simp only [realPeriod,Expr.realEval_cast_rational,he.2.1,he.2.2.2.1,hp,Rat.cast_natCast,
    State.product,State.values,List.prod_cons,Nat.cast_mul]

theorem realScalar_correct (e : StateExpr a ι) (b s : ℕ) (X tb td : ℝ) (outside : List ℕ)
    (x : ι → ℚ) (he : e.Correct x) :
    e.realScalar b s X tb td outside (fun i => (x i:ℝ)) =
      baseScalar X (fun t => (𝓕 SchwartzCutoff.psi) t) (sourceStateBins b s tb td) outside a := by
  have hsmall : (fun i => (e.small i).realEval (fun j => (x j:ℝ))) =
      (fun i => ((a.small.get i).value:ℝ)) := by
    funext i
    rw [Expr.realEval_cast_rational,(he.2.2.2.2 i).2,Rat.cast_natCast]
  simp only [realScalar,realPeriod_correct e outside x he,hsmall,baseScalar,sourceStateBins]

def RealRegular (e : StateExpr a ι) (x : ι → ℝ) : Prop :=
  e.plus.RealRegularAt x ∧ e.minus.RealRegularAt x ∧ ∀ i, (e.small i).RealRegularAt x

theorem realPeriod_contDiffAt [Fintype ι] (e : StateExpr a ι) (outside : List ℕ)
    (x : ι → ℝ) (he : e.RealRegular x) :
    ContDiffAt ℝ ∞ (e.realPeriod outside) x := by
  unfold realPeriod
  apply ContDiffAt.mul contDiffAt_const
  apply (e.plus.contDiffAt_realEval x he.1).mul
  apply (e.minus.contDiffAt_realEval x he.2.1).mul
  simp only [product_realEval,List.map_ofFn,List.prod_ofFn,Function.comp_def]
  exact contDiffAt_prod (fun i _ => (e.small i).contDiffAt_realEval x (he.2.2 i))

theorem realScalar_contDiffAt [Fintype ι] (e : StateExpr a ι) (b s : ℕ) (X tb td : ℝ)
    (outside : List ℕ) (x : ι → ℝ) (he : e.RealRegular x) (hX : 0 < X)
    (hP : 0 < e.realPeriod outside x) (hsmall : ∀ i, 0 < (e.small i).realEval x)
    (houtside : ∀ q ∈ outside, 0 < q) :
    ContDiffAt ℝ ∞ (e.realScalar b s X tb td outside) x := by
  have hp := e.realPeriod_contDiffAt outside x he
  have hsqrt := (ContDiffAt.div (show ContDiffAt ℝ ∞ (fun _ : ι → ℝ => X) x from contDiffAt_const)
    hp hP.ne').sqrt (div_pos hX hP).ne'
  have harg : ContDiffAt ℝ ∞ (fun y => -(a.frequency:ℝ) * X / e.realPeriod outside y) x :=
    contDiffAt_const.div hp hP.ne'
  have hbins := realStateBins_contDiffAt b s tb td a outside
    (fun y i => (e.small i).realEval y) (fun (_ : ι → ℝ) i => (outside.get i:ℝ)) x
    (fun i => (e.small i).contDiffAt_realEval x (he.2.2 i))
    (fun _ => contDiffAt_const) hsmall (fun i => by
      exact_mod_cast houtside (outside.get i) (List.get_mem outside i))
  exact (((Complex.ofRealCLM.contDiff.contDiffAt.comp x hsqrt).mul
    (((𝓕 SchwartzCutoff.psi).smooth ⊤).contDiffAt.comp x harg))).mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x hbins)

end Ostmann.Arithmetic.HistorySymbolicState.StateExpr

end

end OAI
