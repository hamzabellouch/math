import OAI.Dynamics.StandardMap.GraphDerivativeUpgrade

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

noncomputable def tVariation (v dv : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n+2 => v (n+1)*tVariation v dv (n+1)-tVariation v dv n+dv (n+1)*tSolution v (n+1)

lemma hasDerivAt_tSolution_family (v : ℝ → ℕ → ℝ) (dv : ℕ → ℝ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (fun r => v r i) (dv i) x) (n : ℕ) :
    HasDerivAt (fun r => tSolution (v r) n) (tVariation (v x) dv n) x := by
  induction n using Nat.twoStepInduction with
  | zero => exact hasDerivAt_const x 0
  | one => exact hasDerivAt_const x 1
  | more n h0 h1 =>
    have hh:=((hv (n+1)).mul h1).sub h0
    convert! hh using 1
    change v x (n+1)*tVariation (v x) dv (n+1)-tVariation (v x) dv n+dv (n+1)*tSolution (v x) (n+1)=_
    ring

lemma tVariation_wronskian (v dv : ℕ → ℝ) (J n : ℕ) :
    dirichletSolution v J (n+1)*tVariation v dv (n+2)-
      dirichletSolution v J (n+2)*tVariation v dv (n+1)=
        ∑ i ∈ Finset.range (n+1), dirichletSolution v J (i+1)*dv (i+1)*tSolution v (i+1) := by
  induction n with
  | zero => simp [tVariation,dirichletSolution,linearSolution,tSolution]
  | succ n ih =>
    rw [Finset.sum_range_succ,← ih]
    rw [show n+1+1=n+2 by omega,show n+1+2=(n+1)+2 by omega]
    rw [show tVariation v dv (n+1+2)=v (n+2)*tVariation v dv (n+2)-tVariation v dv (n+1)+dv (n+2)*tSolution v (n+2) by rfl,
      dirichletSolution_step v J (n+1)]
    ring

lemma tVariation_div_terminal (v dv : ℕ → ℝ) (n : ℕ) (ht : tSolution v (n+1) ≠ 0) :
    tVariation v dv (n+1)/tSolution v (n+1)=
      ∑ i ∈ Finset.range n, tSolution v (i+1)*dirichletSolution v (n+1) (i+1)*dv (i+1) := by
  cases n with
  | zero => simp [tVariation]
  | succ n =>
    have hh:=tVariation_wronskian v dv (n+1+1) n
    rw [dirichletSolution_boundary v (n+1+1) ht,zero_mul,sub_zero] at hh
    have hw:=solution_wronskian v 1 (boundaryValue v (n+1+1)) (n+1)
    change dirichletSolution v (n+1+1) (n+1)*tSolution v (n+1+1)-
      dirichletSolution v (n+1+1) (n+1+1)*tSolution v (n+1)=1 at hw
    rw [dirichletSolution_boundary v (n+1+1) ht,zero_mul,sub_zero] at hw
    have hu : dirichletSolution v (n+1+1) (n+1)=1/tSolution v (n+1+1) := (eq_div_iff ht).mpr hw
    rw [hu] at hh
    calc
      _ = (1/tSolution v (n+1+1))*tVariation v dv (n+1+1) := by ring
      _ = _ := hh
      _ = _ := by apply Finset.sum_congr rfl; intro i hi; ring

lemma hasDerivAt_log_tSolution_family (v : ℝ → ℕ → ℝ) (dv : ℕ → ℝ) (x : ℝ)
    (hv : ∀ i, HasDerivAt (fun r => v r i) (dv i) x) (n : ℕ)
    (ht : tSolution (v x) (n+1) ≠ 0) :
    HasDerivAt (fun r => Real.log |tSolution (v r) (n+1)|)
      (∑ i ∈ Finset.range n, tSolution (v x) (i+1)*dirichletSolution (v x) (n+1) (i+1)*dv (i+1)) x := by
  have hh := (hasDerivAt_tSolution_family v dv x hv (n+1)).log ht
  rw [tVariation_div_terminal (v x) dv n ht] at hh
  simpa only [Real.log_abs] using hh
end StandardMapEntropy

end OAI
