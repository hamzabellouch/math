import Mathlib.Analysis.Calculus.Deriv.Star
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightAtoms
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightBinZero
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSmooth

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
open scoped ContDiff Topology
variable {ι : Type*}

def realHistorySupportWeight (b s : ℕ) (tb td G : ℝ) (outside : List ℕ) (x : ι → ℝ) :
    {l : ℕ} → (h : History l) → TreeExpr ι h → ℝ
  | _, .leaf a, e => realStateBins b s tb td a outside (fun j => (e.small j).realEval x)
      (fun j => (outside.get j:ℝ))
  | _, .node _ _ _ _ _ left right, e =>
      giantCell G ((treeRoot left e.2.1).plus.realEval x) *
        realHistorySupportWeight b s tb td G outside x left e.2.1 *
        realHistorySupportWeight b s tb td G outside x right e.2.2

theorem realHistorySupportWeight_bounds (b s : ℕ) (tb td G : ℝ) (outside : List ℕ) (x : ι → ℝ)
    {l : ℕ} (h : History l) (e : TreeExpr ι h) :
    0 ≤ realHistorySupportWeight b s tb td G outside x h e ∧
      realHistorySupportWeight b s tb td G outside x h e ≤ 1 := by
  induction h with
  | leaf a => exact realStateBins_bounds _ _ _ _ _ _ _ _
  | node a p u hp hm left right il ir =>
    obtain ⟨hl,hl1⟩ := il e.2.1
    obtain ⟨hr,hr1⟩ := ir e.2.2
    obtain ⟨hc,hc1⟩ := giantCell_bounds G ((treeRoot left e.2.1).plus.realEval x)
    refine ⟨mul_nonneg (mul_nonneg hc hl) hr, ?_⟩
    calc
      _ ≤ (1 * 1) * 1 :=
        mul_le_mul (mul_le_mul hc1 hl1 hl zero_le_one) hr1 hr (by norm_num)
      _ = 1 := by norm_num

theorem realHistoryScalar_eq_zero_of_support_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) (x : ι → ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hz : realHistorySupportWeight b s tb td G outside x h e = 0) :
    realHistoryScalar b s X tb td G outside x h e = 0 := by
  induction h with
  | leaf a =>
    change realStateBins b s tb td a outside _ _ = 0 at hz
    simp only [realHistoryScalar,StateExpr.realScalar,hz,Complex.ofReal_zero,mul_zero]
  | node a p u hp hm left right il ir =>
    obtain hc | hr := mul_eq_zero.mp hz
    · obtain hc | hl := mul_eq_zero.mp hc
      · simp only [realHistoryScalar,hc,Complex.ofReal_zero,zero_mul]
      · simp only [realHistoryScalar,il _ hl,mul_zero,zero_mul]
    · simp only [realHistoryScalar,ir _ hr,star_zero,mul_zero]

theorem realHistorySupportWeight_ne_zero_of_scalar_ne_zero (b s : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) (x : ι → ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hz : realHistoryScalar b s X tb td G outside x h e ≠ 0) :
    realHistorySupportWeight b s tb td G outside x h e ≠ 0 :=
  fun he => hz (realHistoryScalar_eq_zero_of_support_zero b s X tb td G outside x h e he)

theorem logCurve_contDiff [Fintype ι] [DecidableEq ι] (x : ι → ℝ) (i : ι) :
    ContDiff ℝ ∞ (Expr.logCurve x i) := by
  apply contDiff_pi.mpr
  intro j
  unfold Expr.logCurve
  split_ifs <;> fun_prop

theorem encode_realHistoryScalar_logCurve_differentiableAt [Fintype ι] [DecidableEq ι]
    (b s : ℕ) (X tb td G : ℝ) (hX : 0 < X) (outside : List ℕ)
    (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside)
    (e : StateExpr h.root ι) (comp : InternalKey h → Expr ι) (x : ι → ℝ) (i : ι)
    (he : e.RealRegular x) (hsmall : ∀ j, 0 < (e.small j).realEval x)
    (hplus : 0 < e.plus.realEval x) (hminus : 0 < e.minus.realEval x)
    (hc : ∀ j, (comp j).RealRegularAt x) (hcp : ∀ j, 0 < (comp j).realEval x) :
    DifferentiableAt ℝ (fun t => realHistoryScalar b s X tb td G outside (Expr.logCurve x i t)
      h (encode V outside h hs e comp)) 0 := by
  have hf := encode_realHistoryScalar_contDiffAt b s X tb td G hX outside houtside h hs e comp x
    he hsmall hplus hminus hc hcp
  have hf' : ContDiffAt ℝ ∞ (fun y => realHistoryScalar b s X tb td G outside y h
      (encode V outside h hs e comp)) (Expr.logCurve x i 0) := by
    simpa only [Expr.logCurve_zero] using hf
  have hh := hf'.comp (0:ℝ) (logCurve_contDiff x i).contDiffAt
  exact hh.differentiableAt (by simp)

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
