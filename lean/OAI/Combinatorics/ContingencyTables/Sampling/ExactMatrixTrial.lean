import OAI.Combinatorics.ContingencyTables.Sampling.ExactIntegerOnline
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableBox
import OAI.Combinatorics.ContingencyTables.Sampling.ExactIntegerPhysical

namespace OAI

/-! # Returning a matrix from the exact integer-weighted trial -/

namespace ContingencyTables.ExactMatrixTrial
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open DensePrograms ProfilePrograms

/-- Enumerated candidates together with a feasible fallback. -/
abbrev Lookup := List (Option MatrixCode)×MatrixCode
abbrev Input := Lookup×List ℕ

def lookup (z : Lookup×ℕ) : MatrixCode := (z.1.1.getD z.2 none).getD z.1.2

def lookupRealizer : Realizer lookup :=
  composition (f := fun z : Lookup×ℕ => (z.1.2,z.1.1.getD z.2 none))
    (g := fun z : MatrixCode×Option MatrixCode => z.2.getD z.1)
    (pair (composition first second)
      (composition (pair (composition first first) second) (getDFast none)))
    FirstSuccessProgram.defaultRealizer

lemma polynomial_lookup : PolynomialTime lookupRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) (polynomial_getDFast none))) FirstSuccessProgram.polynomial_default

def decode (z : Lookup×Option ℕ) : Option MatrixCode :=
  z.2.map (fun i => lookup (z.1,i))

def decodeRealizer : Realizer decode :=
  (choose (composition second FirstSuccessProgram.isSomeRealizer)
    (composition (composition
      (pair first (composition (pair (constant (0:ℕ)) second) FirstSuccessProgram.defaultRealizer))
      lookupRealizer) some) (constant none)).congr (by
        intro z
        rcases z with ⟨cache,o⟩
        cases o <;> rfl)

lemma polynomial_decode : PolynomialTime decodeRealizer := by
  unfold decodeRealizer
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition polynomial_second FirstSuccessProgram.polynomial_isSome)
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_second)
        FirstSuccessProgram.polynomial_default)) polynomial_lookup) polynomial_some)
    (polynomial_constant none)

def trial (z : Input) : Experiment (Option MatrixCode) :=
  (ExactIntegerOnline.trial z.2).map (fun i => decode (z.1,i))

noncomputable def trialRealizer : OnlineTree.Realizer trial :=
  (OnlineTree.composition
    (OnlineTree.pair (OnlineTree.deterministic first)
      (OnlineTree.composition (OnlineTree.deterministic second) ExactIntegerOnline.trialRealizer))
    (OnlineTree.deterministic decodeRealizer)).congr (by
      intro z g
      simp only [Experiment.mean_bind,Experiment.mean,Experiment.mean_map,trial])

lemma polynomial_trial : OnlineTree.PolynomialTime trialRealizer := by
  unfold trialRealizer
  apply OnlineTree.work_congr
  exact OnlineTree.polynomial_composition
    (OnlineTree.polynomial_pair (OnlineTree.polynomial_deterministic polynomial_first)
      (OnlineTree.polynomial_composition (OnlineTree.polynomial_deterministic polynomial_second)
        ExactIntegerOnline.polynomial_trial))
    (OnlineTree.polynomial_deterministic polynomial_decode)

noncomputable section
open ExactIntegerChoice ResidualMixture
open scoped BigOperators Classical

lemma trial_mean {K : ℕ} (candidates : Lookup) (w : Fin K → ℕ)
    (hw : 0<totalWeight w) (g : Option MatrixCode → ℚ) :
    (trial (candidates,List.ofFn w)).mean g=
      ∑ y : Option (Fin K),
        (trialLaw w hw (Nat.le_pow_clog (by decide : 1<2) (totalWeight w))).mass y*
          g (y.map (fun i => lookup (candidates,i.val))) := by
  rw [trial,Experiment.mean_map,ExactIntegerOnline.trial_mean w hw]
  apply Finset.sum_congr rfl
  intro y _
  cases y <;> rfl

lemma trial_failure {K : ℕ} (candidates : Lookup) (w : Fin K → ℕ)
    (hw : 0<totalWeight w) :
    (trial (candidates,List.ofFn w)).mean (fun o => if o=none then 1 else 0)=
      failure w (Q := 2^(Nat.clog 2 (totalWeight w))) := by
  rw [trial_mean _ w hw,Fintype.sum_option]
  simp only [Option.map_none,ite_true,Option.map_some,reduceCtorEq,ite_false,mul_zero,
    Finset.sum_const_zero,add_zero,mul_one,trialLaw_none]

lemma prefix_mean {K : ℕ} (candidates : Lookup) (w : Fin K → ℕ)
    (hw : 0<totalWeight w) (N : ℕ) (g : Option MatrixCode → ℚ) :
    (OnlineIntegerRetry.prefixExperiment (f := trial) (candidates,List.ofFn w) N).mean g=
      ∑ y : Option (Fin K),
        (retryIntegerLaw w hw (Nat.le_pow_clog (by decide : 1<2) (totalWeight w)) N).mass y*
          g (y.map (fun i => lookup (candidates,i.val))) :=
  ExactIntegerOnline.prefix_mean trial (candidates,List.ofFn w) _ _
    (trial_mean candidates w hw) N g

lemma prefix_failure {K : ℕ} (candidates : Lookup) (w : Fin K → ℕ)
    (hw : 0<totalWeight w) (N : ℕ) :
    (OnlineIntegerRetry.prefixExperiment (f := trial) (candidates,List.ofFn w) N).mean
      (fun o => if o=none then 1 else 0)≤(1/2:ℚ)^N := by
  rw [prefix_mean candidates w hw,Fintype.sum_option]
  simp only [Option.map_none,ite_true,Option.map_some,reduceCtorEq,ite_false,mul_zero,
    Finset.sum_const_zero,add_zero,mul_one]
  exact retryIntegerLaw_failure_bound w hw _
    (clog_power_lt_twice (totalWeight w) hw) N

/-- Exact weighted matrix selection has a summable physical halting tail. -/
theorem expected_time {K : ℕ} (candidates : Lookup) (w : Fin K → ℕ)
    (hw : 0<totalWeight w) (s : TreeData.Data) (H : ℕ)
    (hH : StackCost.StackBound
      (OnlineTree.initial (OnlineIntegerRetry.program trialRealizer)
        (TreeTyped.encode (candidates,List.ofFn w)) s).stk H) :
    Summable (PhysicalRetryTail.tail (OnlineRetryRuntime.machineTable trialRealizer)
      (OnlineRetryRuntime.initialCfg trialRealizer (candidates,List.ofFn w) s)) ∧
    (∑' t,PhysicalRetryTail.tail (OnlineRetryRuntime.machineTable trialRealizer)
      (OnlineRetryRuntime.initialCfg trialRealizer (candidates,List.ofFn w) s) t)≤
        2*(OnlineRetryRuntime.attemptBound trialRealizer (candidates,List.ofFn w) H:ℝ) :=
  OnlineRetryRuntime.expected_time trialRealizer (candidates,List.ofFn w) s H hH
    (prefix_failure candidates w hw)

end
end ContingencyTables.ExactMatrixTrial

end OAI
