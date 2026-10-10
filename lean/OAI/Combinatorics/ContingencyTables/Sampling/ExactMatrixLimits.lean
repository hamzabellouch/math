import OAI.Combinatorics.ContingencyTables.Sampling.ExactMatrixTrial

namespace OAI

/-! # Limiting output law of the executed matrix rejection loop -/

namespace ContingencyTables.ExactMatrixTrial
open MatchingFPRAS MatchingFPRAS.PhysicalStream DensePrograms
open ExactIntegerChoice ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section

lemma prefix_mass {K : ℕ} (candidates : Lookup) (w : Fin K → ℕ)
    (hw : 0<totalWeight w) (N : ℕ) (X : MatrixCode) :
    (OnlineIntegerRetry.prefixExperiment (f := trial) (candidates,List.ofFn w) N).mean
      (fun o => if o=some X then 1 else 0)=
      ∑ i : Fin K,if lookup (candidates,i.val)=X then
        (retryIntegerLaw w hw (Nat.le_pow_clog (by decide : 1<2) (totalWeight w)) N).mass (some i)
        else 0 := by
  rw [prefix_mean candidates w hw,Fintype.sum_option]
  simp only [Option.map_none,reduceCtorEq,ite_false,mul_zero,zero_add,Option.map_some,
    Option.some.injEq,mul_ite,mul_one,mul_zero]

/-- The integer rejection loop tends to the exact weighted pushforward,
including repeated matrix codes in a candidate list. -/
theorem prefix_limit {K : ℕ} (candidates : Lookup) (w : Fin K → ℕ)
    (hw : 0<totalWeight w) (X : MatrixCode) :
    Filter.Tendsto (fun N =>
      ((OnlineIntegerRetry.prefixExperiment (f := trial) (candidates,List.ofFn w) N).mean
        (fun o => if o=some X then 1 else 0):ℝ))
      Filter.atTop (nhds ((∑ i : Fin K,if lookup (candidates,i.val)=X then normalized w i else 0:ℚ):ℝ)) := by
  simp_rw [prefix_mass candidates w hw,Rat.cast_sum]
  apply tendsto_finsetSum
  intro i _
  by_cases hi : lookup (candidates,i.val)=X
  · simp only [hi,ite_true]
    exact retryIntegerLaw_limit w hw _ (clog_power_lt_twice (totalWeight w) hw) i
  · simp only [hi,ite_false,Rat.cast_zero]
    exact tendsto_const_nhds

end
end ContingencyTables.ExactMatrixTrial

end OAI
