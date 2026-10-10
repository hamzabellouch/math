import OAI.NumberTheory.Jacobsthal.Probability.RepeatedPairEvents

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPairRow
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain ActualProcessCoupling
open ActualCoupledHistories ActualFlagInvariant PersistentFailureFlag
open RepeatedStepRowBound RepeatedPairEvents FiniteHistoryPairLaw
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels

attribute [local instance] Classical.propDecidable

theorem repeatBudget_nonneg {U X xi w mesh : ℝ} (hU : 0 ≤ U) (hX : 0 < X)
    (hxi : 0 ≤ xi) (hw : 1 < w) (hm : 0 ≤ mesh) : 0 ≤ repeatBudget U X xi w mesh := by
  have hC := repeatDensityConstant_pos
  have hlog := Real.log_pos hw
  unfold repeatBudget
  positivity

variable {w ell S : ℝ} {start : Node}
variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem repeated_pair_row_uniform {top xi U X mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hU : 0 ≤ U) (hX : 0 < X)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top)
    (N : ℕ) (G : Set (ChainState w ell S start)) (x : FlagState (JointState w ell S start)) :
    pairProbability (sourceTransition hwn hell hS0 hS hr hs hsS mesh)
      (goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N) x ≤
        ENNReal.ofReal (repeatBudget U X xi w mesh) := by
  let E := goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N
  by_cases hmem : ((Prod.mk x) ⁻¹' E).Nonempty
  · obtain ⟨y,hy⟩ := hmem
    obtain ⟨h,hleft,hne,hparent,_hG⟩ := primeRepeatPair_left _ hy.2.2
    rcases x with ⟨⟨px,rx⟩,flag⟩
    change px=some h at hleft
    subst px
    cases rx with
    | inr u => exact False.elim hy.1
    | inl z =>
      have hsub : ((Prod.mk ((some h,Sum.inl z),flag)) ⁻¹' E) ⊆
          goodRepeatNext (label (zero_lt_one.trans hw) htop hxi) X (Real.log start.gap) mesh N h := by
        intro y' hy'
        exact ⟨hy'.2.1,primeRepeatPair_next _ h y' hy'.2.2⟩
      exact (measure_mono hsub).trans
        (good_repeat_next_row hwn hell hS0 hS hr hs hsS hw htop hxi hU hX hm hmesh hcap N h hne z flag hy.1 hparent)
  · have he : ((Prod.mk x) ⁻¹' E)=∅ := Set.not_nonempty_iff_eq_empty.mp hmem
    change sourceTransition hwn hell hS0 hS hr hs hsS mesh x ((Prod.mk x) ⁻¹' E) ≤ _
    rw [he,measure_empty]
    exact zero_le

theorem repeated_pair_row_gated {top xi U X mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hU : 0 ≤ U) (hX : 0 < X)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top)
    (N : ℕ) (G : Set (ChainState w ell S start)) (x : FlagState (JointState w ell S start)) :
    pairProbability (sourceTransition hwn hell hS0 hS hr hs hsS mesh)
      (goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N) x ≤
        ENNReal.ofReal (repeatBudget U X xi w mesh*(if x.1.1 ∈ G then 1 else 0)) := by
  by_cases hx : x.1.1 ∈ G
  · rw [ite_eq_left hx,mul_one]
    exact repeated_pair_row_uniform hwn hell hS0 hS hr hs hsS hw htop hxi hU hX hm hmesh hcap N G x
  · rw [ite_eq_right hx,mul_zero,ENNReal.ofReal_zero]
    let E := goodRepeatPair (label (zero_lt_one.trans hw) htop hxi) X U G (Real.log start.gap) mesh N
    have he : ((Prod.mk x) ⁻¹' E)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨h,_he,_hn,_hU,hG⟩ := primeRepeatPair_left _ hy.2.2
      exact hx hG
    change sourceTransition hwn hell hS0 hS hr hs hsS mesh x ((Prod.mk x) ⁻¹' E) ≤ 0
    rw [he,measure_empty]
end NumberTheoryLean.RepeatedPairRow


end Erdos970

end OAI
