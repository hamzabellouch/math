import OAI.NumberTheory.Jacobsthal.Estimates.RepeatedPairRow

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPairProbability
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain ActualProcessCoupling
open ActualCoupledHistories ActualFlagInvariant ActualSuccessfulHistories PersistentFailureFlag
open RepeatedStepRowBound RepeatedPairEvents RepeatedPairRow
open FiniteHistoryTransport FiniteHistoryOccurrence FiniteHistoryPairLaw FinitePairOccurrence
open PrimeCompactVisits PrimeHistoryCompactCount
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

attribute [local instance] Classical.propDecidable
variable {w ell S : ℝ} {start : Node}

noncomputable def rawRepeatPair {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start)) :
    Set (FlagState (JointState w ell S start) × FlagState (JointState w ell S start)) :=
  {xy | primeRepeatPair lab X U G (xy.1.1.1,xy.2.1.1)}

theorem rawRepeatPair_measurable {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start)) :
    MeasurableSet (rawRepeatPair lab X U G) := by
  have hm : Measurable (fun xy : FlagState (JointState w ell S start) × FlagState (JointState w ell S start) =>
      (xy.1.1.1,xy.2.1.1)) := by fun_prop
  have hp : MeasurableSet {pq : ChainState w ell S start × ChainState w ell S start | primeRepeatPair lab X U G pq} :=
    (Set.to_countable _).measurableSet
  exact hm hp

noncomputable def compactParentGate (L : ℝ) : Set (ChainState w ell S start) :=
  {p | match p with | none => False | some h => h.node.gap ≤ L}

theorem compact_gate_visit (L : ℝ) (p : ChainState w ell S start) :
    (if p ∈ compactParentGate L then (1:ℝ) else 0)=visit L p := by
  cases p with
  | none => simp [compactParentGate,visit]
  | some h => rfl

variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem raw_repeat_good_on_success {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start))
    {mesh : ℝ} (hm : 0 < mesh) (N : ℕ) :
    ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      (last N h).2=false → h ∈ pairOccurrence (rawRepeatPair lab X U G) N →
        h ∈ pairOccurrence (goodRepeatPair lab X U G (Real.log start.gap) mesh N) N := by
  filter_upwards [sourceHistory_success_good hwn hell hS0 hS hr hs hsS hm N] with h hh
  intro hf hraw
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hraw
  apply Set.mem_iUnion.mpr
  refine ⟨j,?_,?_,hj⟩
  · exact goodAt_enlarge hm.le j.isLt.le _ (hh hf ⟨j.1,Finset.mem_Iic.mpr j.isLt.le⟩)
  · exact goodAt_enlarge hm.le (show j.1+1 ≤ N by have := j.isLt; omega) _
      (hh hf ⟨j.1+1,Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩)

theorem raw_repeat_probability_le_good {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start))
    {mesh : ℝ} (hm : 0 < mesh) (N : ℕ) :
    sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N (pairOccurrence (rawRepeatPair lab X U G) N) ≤
      FlaggedSourceStart.sourceLaw hwn hell hS0 hS hr hs hsS mesh N failed+
        sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N
          (pairOccurrence (goodRepeatPair lab X U G (Real.log start.gap) mesh N) N) := by
  have hsub : ∀ᵐ h ∂sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N,
      h ∈ pairOccurrence (rawRepeatPair lab X U G) N → h ∈ {h | (last N h).2=true} ∪
        pairOccurrence (goodRepeatPair lab X U G (Real.log start.gap) mesh N) N := by
    filter_upwards [raw_repeat_good_on_success hwn hell hS0 hS hr hs hsS lab X U G hm N] with h hh
    intro hp
    cases hf : (last N h).2 with
    | false => exact Or.inr (hh hf hp)
    | true => exact Or.inl hf
  calc
    _ ≤ sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N ({h | (last N h).2=true} ∪
        pairOccurrence (goodRepeatPair lab X U G (Real.log start.gap) mesh N) N) := measure_mono_ae hsub
    _ ≤ _ := by
      rw [← sourceHistory_failure_probability hwn hell hS0 hS hr hs hsS mesh N]
      exact measure_union_le _ _

theorem good_repeat_probability_uniform {top xi U X mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hU : 0 ≤ U) (hX : 0 < X)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top)
    (N : ℕ) (G : Set (ChainState w ell S start)) :
    sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N
      (pairOccurrence (goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N) N) ≤
        ENNReal.ofReal ((N:ℝ)*repeatBudget U X xi w mesh) := by
  exact pair_occurrence_of_uniform_row _ (goodRepeatPair_measurable _ _ _ _ _ _ _) N _
    (repeatBudget_nonneg hU hX hxi.le hw hm.le)
    (repeated_pair_row_uniform hwn hell hS0 hS hr hs hsS hw htop hxi hU hX hm hmesh hcap N G)

theorem good_repeat_probability_compact {top xi L mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hL : 0 ≤ L)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top) (N : ℕ) :
    sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N
      (pairOccurrence (goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) 1 L (compactParentGate L)
        (Real.log start.gap) mesh N) N) ≤ ENNReal.ofReal (repeatBudget L 1 xi w mesh*(L+1)) := by
  let A := repeatBudget L 1 xi w mesh
  have hA : 0 ≤ A := repeatBudget_nonneg hL (by norm_num) hxi.le hw hm.le
  apply pair_occurrence_of_budget _ (goodRepeatPair_measurable _ _ _ _ _ _ _) N _
    (fun x : FlagState (JointState w ell S start) => A*visit L x.1.1)
    (fun x => mul_nonneg hA (visit_nonneg L _)) (A*(L+1))
  · intro x
    have hh := repeated_pair_row_gated hwn hell hS0 hS hr hs hsS hw htop hxi hL (show (0:ℝ)<1 by norm_num) hm hmesh hcap N
      (compactParentGate L) x
    simpa only [compact_gate_visit] using hh
  · filter_upwards [sourceHistory_compact_count hwn hell hS0 hS hr hs hsS hL mesh N] with h hh
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hh hA

theorem raw_repeat_probability_compact {top xi L mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hL : 0 ≤ L)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top) (N : ℕ) :
    sourceHistoryLaw hwn hell hS0 hS hr hs hsS mesh N
      (pairOccurrence (rawRepeatPair (label (zero_lt_one.trans hw) htop hxi) 1 L (compactParentGate L)) N) ≤
        FlaggedSourceStart.sourceLaw hwn hell hS0 hS hr hs hsS mesh N failed+
          ENNReal.ofReal (repeatBudget L 1 xi w mesh*(L+1)) :=
  (raw_repeat_probability_le_good hwn hell hS0 hS hr hs hsS _ 1 L (compactParentGate L) hm N).trans
    (add_le_add le_rfl (good_repeat_probability_compact hwn hell hS0 hS hr hs hsS hw htop hxi hL hm hmesh hcap N))
end NumberTheoryLean.RepeatedPairProbability


end Erdos970

end OAI
