import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightAtoms
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightProductDeriv

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Characters.RationalHistory
open scoped ContDiff
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def logSumCell (S : Finset ι) (q : ι → κ) (x : κ → ℝ) (i : κ) (c t : ℝ) : ℝ :=
  smoothPartition ((∑ j ∈ S, Real.log (Expr.logCurve x i t (q j))) - c)

theorem logSumCell_hasDerivAt {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (q : ι → κ) (x : κ → ℝ) (i : κ) (c : ℝ)
    (hx : ∀ j ∈ S, 0 < x (q j)) :
    HasDerivAt (logSumCell S q x i c)
      (deriv smoothPartition ((∑ j ∈ S, Real.log (x (q j))) - c) *
        (∑ j ∈ S, if q j = i then (1:ℝ) else 0)) 0 := by
  have hj (j : ι) (hj : j ∈ S) :
      HasDerivAt (fun t => Real.log (Expr.logCurve x i t (q j))) (if q j = i then (1:ℝ) else 0) 0 := by
    have h := (Expr.hasDerivAt_logCurve (.atom (q j)) x i trivial).log (by
      simpa only [Expr.realEval,Expr.logCurve_zero] using (hx j hj).ne')
    by_cases he : q j = i
    · simpa only [Expr.realEval,Expr.logDerivative,Expr.logCurve_zero,ite_eq_left he,
        div_self (hx j hj).ne'] using h
    · simpa only [Expr.realEval,Expr.logDerivative,Expr.logCurve_zero,ite_eq_right he,zero_div] using h
  have hsum := (HasDerivAt.fun_sum hj).sub_const c
  have hφ := ((smoothPartition_contDiff.differentiable (by simp))
    ((∑ j ∈ S, Real.log (x (q j))) - c)).hasDerivAt
  have hcomp := hφ.comp_of_eq 0 hsum (by simp only [Expr.logCurve_zero])
  simpa only [logSumCell,Function.comp_def] using! hcomp

theorem logSumCell_deriv_bound (S : Finset ι) (q : ι → κ) (x : κ → ℝ) (i : κ) (c D : ℝ)
    (hx : ∀ j ∈ S, 0 < x (q j)) (hD : 0 ≤ D)
    (hφ : ∀ z, |deriv smoothPartition z| ≤ D) :
    |deriv (logSumCell S q x i c) 0| ≤ D * S.card := by
  rw [(logSumCell_hasDerivAt S q x i c hx).deriv,abs_mul]
  have hn : 0 ≤ ∑ j ∈ S, if q j = i then (1:ℝ) else 0 := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hb : (∑ j ∈ S, if q j = i then (1:ℝ) else 0) ≤ S.card := by
    calc
      _ ≤ ∑ _j ∈ S, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
      _ = _ := by simp
  rw [abs_of_nonneg hn]
  exact mul_le_mul (hφ _) hb hn hD

theorem smoothPartition_deriv_uniform : ∃ D : ℝ, 0 < D ∧ ∀ z, |deriv smoothPartition z| ≤ D := by
  obtain ⟨M,hM,hb⟩ := smoothPartition_deriv_sub_bound
  refine ⟨M+1,by positivity,?_⟩
  intro z
  calc
    _ = |(deriv smoothPartition z-smoothPartition z)+smoothPartition z| := by congr 1; ring
    _ ≤ |deriv smoothPartition z-smoothPartition z| + |smoothPartition z| := abs_add_le _ _
    _ ≤ M+1 := add_le_add (hb z) (by rw [abs_of_nonneg (smoothPartition_nonneg z)]; exact smoothPartition_le_one z)

end Ostmann.Arithmetic

end

end OAI
