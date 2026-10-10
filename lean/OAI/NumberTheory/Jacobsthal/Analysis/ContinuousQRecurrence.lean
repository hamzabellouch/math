import OAI.NumberTheory.Jacobsthal.Estimates.GateIterates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

theorem gate_truncatedReference (N : ℕ) (i : Side) (r b : ℝ) :
    gate (truncatedReference N) i r b=
      ∑ n ∈ Finset.range N,(-1:ℝ)^n*boundaryTerm (n+1) i r b := by
  change gate (fun j s t => ∑ n ∈ Finset.range N,(-1:ℝ)^n*boundaryTerm n j s t) i r b=_
  rw [gate_sum N (fun n j s t => (-1:ℝ)^n*boundaryTerm n j s t)
    (fun n j => continuous_const.mul (boundaryTerm_continuous n j))]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [gate_mul]
  rfl

theorem truncatedReference_recurrence (N : ℕ) (i : Side) (r b : ℝ) :
    truncatedReference (N+1) i r b=1-gate (truncatedReference N) i r b := by
  have hfirst : truncatedReference (N+1) i r b=
      (∑ n ∈ Finset.range N,(-1:ℝ)^(n+1)*boundaryTerm (n+1) i r b)+1 := by
    rw [truncatedReference,Finset.sum_range_succ']
    simp only [pow_zero,show boundaryTerm 0 i r b=(1:ℝ) by rfl,one_mul]
  have hs (n : ℕ) : (-1:ℝ)^(n+1)*boundaryTerm (n+1) i r b=
      -((-1:ℝ)^n*boundaryTerm (n+1) i r b) := by rw [pow_succ]; ring
  rw [hfirst]
  simp_rw [hs]
  rw [Finset.sum_neg_distrib,← gate_truncatedReference]
  ring

theorem boundaryReference_recurrence (i : Side) (r b : ℝ) :
    boundaryReference i r b=1-gate boundaryReference i r b := by
  let N := referenceDepth r
  have hN : 2 ≤ N := (referenceDepth_bounds r).1
  have hrN : r ≤ (N:ℝ)-1 := (referenceDepth_bounds r).2
  have hq : boundaryReference i r b=truncatedReference (N+1) i r b :=
    boundaryReference_eq_truncated (N+1) (by omega) i (by push_cast; linarith)
  have hchild : gate boundaryReference i r b=gate (truncatedReference N) i r b := by
    unfold gate
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
    dsimp only
    rw [boundaryReference_eq_truncated N hN i.flip (by linarith [hx.1] : r-x ≤ (N:ℝ)-1)]
  rw [hq,truncatedReference_recurrence,← hchild]

end ErdosContinuousOmission

end

end Erdos970

end OAI
