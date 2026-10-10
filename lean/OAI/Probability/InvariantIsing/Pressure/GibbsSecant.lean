import OAI.Probability.InvariantIsing.Core.Ward

namespace OAI

/-! Endpoint Gibbs averages bound a finite log-partition difference. These
are the convex secant inequalities used to change spectral multiplicities. -/

noncomputable section
open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma log_finitePartition_sub_ge_gibbsAverage
    {S : Type*} [Fintype S] {w : S → ℝ} (hw : GibbsReference w)
    (H K : S → ℝ) :
    gibbsAverage w H (fun s => K s - H s) ≤
      Real.log (finitePartition w K) - Real.log (finitePartition w H) := by
  let Y := fun s => K s - H s
  have hd := hasDerivAt_log_finitePartition hw (t := (0 : ℝ))
    (fun s => (hasDerivAt_const 0 (H s)).add ((hasDerivAt_id 0).mul_const (Y s)))
  have hc := convexOn_log_finitePartition hw H Y
  have hs := hc.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) (by norm_num) hd
  simpa only [slope_def_field, sub_zero, div_one, zero_add, zero_mul, one_mul,
    add_sub_cancel, Y, gibbsAverage, Pi.add_apply, id_eq, add_zero] using hs

lemma log_finitePartition_sub_le_gibbsAverage
    {S : Type*} [Fintype S] {w : S → ℝ} (hw : GibbsReference w)
    (H K : S → ℝ) :
    Real.log (finitePartition w K) - Real.log (finitePartition w H) ≤
      gibbsAverage w K (fun s => K s - H s) := by
  have h := log_finitePartition_sub_ge_gibbsAverage hw K H
  have he : gibbsAverage w K (fun s => H s - K s) =
      -gibbsAverage w K (fun s => K s - H s) := by
    simp only [gibbsAverage, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [he] at h
  linarith

lemma log_finitePartition_secant_bounds
    {S : Type*} [Fintype S] {w : S → ℝ} (hw : GibbsReference w)
    (H K : S → ℝ) :
    gibbsAverage w H (fun s => K s - H s) ≤
      Real.log (finitePartition w K) - Real.log (finitePartition w H) ∧
    Real.log (finitePartition w K) - Real.log (finitePartition w H) ≤
      gibbsAverage w K (fun s => K s - H s) :=
  ⟨log_finitePartition_sub_ge_gibbsAverage hw H K,
    log_finitePartition_sub_le_gibbsAverage hw H K⟩

end InvariantIsing

end

end OAI
