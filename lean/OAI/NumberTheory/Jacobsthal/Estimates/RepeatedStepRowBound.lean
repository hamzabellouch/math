import OAI.NumberTheory.Jacobsthal.Partitions.ActualRepeatedBinStep
import OAI.NumberTheory.Jacobsthal.Probability.SourceTransitionSupport

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedStepRowBound
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain ActualProcessCoupling
open ActualCoupledHistories ActualFlagInvariant PersistentFailureFlag ActualCouplingUpdates
open SourceTransitionSupport CompletedParentInterval ContinuousIntervalUpper
open ContinuousKilledBins
open ActualRepeatedBinStep RepeatedBinGeometry
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosPrimeInputs.HarmonicPrimeMeasure


noncomputable def repeatDensityConstant : ℝ := Classical.choose completed_parent_interval_upper

theorem repeatDensityConstant_pos : 0 < repeatDensityConstant :=
  (Classical.choose_spec completed_parent_interval_upper).1

noncomputable def repeatBudget (U X xi w mesh : ℝ) : ℝ :=
  repeatDensityConstant*(U+2)^2*(U*(xi/Real.log w)/X+2*mesh)

variable {w ell S : ℝ} {start : Node}

def nextRepeat {n : ℕ} (lab : ℕ → Fin n) (X : ℝ) (h : History w ell S start)
    (y : FlagState (JointState w ell S start)) : Prop :=
  match y.1.1 with
  | none => False
  | some k => lab (h.primes.getLastD 0)=lab (k.primes.getLastD 0) ∧ X ≤ k.node.cutoff

theorem nextRepeat_measurable {n : ℕ} (lab : ℕ → Fin n) (X : ℝ) (h : History w ell S start) :
    MeasurableSet {y | nextRepeat lab X h y} := by
  have hm : Measurable (fun y : FlagState (JointState w ell S start) => y.1.1) := measurable_fst.comp measurable_fst
  exact hm (show MeasurableSet {q : ChainState w ell S start | match q with
    | none => False
    | some k => lab (h.primes.getLastD 0)=lab (k.primes.getLastD 0) ∧ X ≤ k.node.cutoff} from trivial)

noncomputable def goodRepeatNext {n : ℕ} (lab : ℕ → Fin n) (X v mesh : ℝ) (N : ℕ)
    (h : History w ell S start) : Set (FlagState (JointState w ell S start)) :=
  {y | GoodAt v mesh N y.1 ∧ nextRepeat lab X h y}

theorem goodRepeatNext_measurable {n : ℕ} (lab : ℕ → Fin n) (X v mesh : ℝ) (N : ℕ)
    (h : History w ell S start) : MeasurableSet (goodRepeatNext lab X v mesh N h) :=
  (measurable_fst (GoodAt_measurable v mesh N)).inter (nextRepeat_measurable lab X h)

variable (hwn : normalizationThreshold ≤ w) (hell : 1 ≤ ell) (hS0 : 0 ≤ S)
variable (hS : S ≤ (Real.log w)^3) (hr : 0 < start.gap)
variable (hs : Valid start.side start.ratio) (hsS : start.ratio ≤ S)

theorem good_repeat_next_row {top xi U X mesh : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hU : 0 ≤ U) (hX : 0 < X)
    (hm : 0 < mesh) (hmesh : mesh ≤ 1) (hcap : w^start.cutoff=top)
    (N : ℕ) (h : History w ell S start) (hne : h.primes ≠ []) (z : CostState) (flag : Bool)
    (hgood : GoodAt (Real.log start.gap) mesh N (some h,Sum.inl z)) (hparent : h.node.ratio ≤ U) :
    sourceTransition hwn hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag)
      (goodRepeatNext (label (zero_lt_one.trans hw) htop hxi) X (Real.log start.gap) mesh N h) ≤
        ENNReal.ofReal (repeatBudget U X xi w mesh) := by
  let a := minRatio (stateSide z.1) (stateRatio z.1)
  let H := U*(xi/Real.log w)/X+2*mesh
  have hh0 : 0 ≤ xi/Real.log w := div_nonneg hxi.le (Real.log_pos hw).le
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hzU : stateRatio z.1 ≤ U+1 := by linarith [(abs_le.mp hgood.2.2.1).1]
  have hT : MeasurableSet (Sum.inl '' closedCostBin a (a+H) : Set (CemeteryKernel.Space CostState)) :=
    (closedCostBin_measurable a (a+H)).inl_image
  have hdom : ∀ᵐ y ∂sourceTransition hwn hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag),
      y ∈ goodRepeatNext (label (zero_lt_one.trans hw) htop hxi) X (Real.log start.gap) mesh N h →
        y.1.2 ∈ Sum.inl '' closedCostBin a (a+H) := by
    filter_upwards [sourceTransition_live_support hwn hell hS0 hS hr hs hsS mesh h z flag] with y hsupport
    intro hy
    rcases y with ⟨⟨py,ry⟩,fy⟩
    cases py with
    | none => exact False.elim hy.2
    | some k =>
      cases ry with
      | inr u => exact False.elim hy.1
      | inl q =>
        obtain ⟨p,hp,rfl⟩ := hsupport.1
        have hl : label (zero_lt_one.trans hw) htop hxi (h.primes.getLastD 0)=label (zero_lt_one.trans hw) htop hxi p := by
          simpa only [History.append_primes,List.getLastD_concat] using hy.2.1
        have hx : X ≤ primeExponent w p := by simpa only [History.append_node,step] using hy.2.2
        have hslack := (actual_same_bin_slack hw htop hell hxi hr hs hcap h hne p hp hl).2
        have hupper : (h.append p hp).node.ratio-(h.node.ratio-1) ≤ U*(xi/Real.log w)/X := by
          calc
            _ ≤ h.node.ratio*(xi/Real.log w)/primeExponent w p := hslack
            _ ≤ U*(xi/Real.log w)/primeExponent w p :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hparent hh0) (hX.trans_le hx).le
            _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hU hh0) hX hx
        have hInt := matched_repeat_interval (stateSide z.1) hgood.2.2.1 hy.1.2.2.1 hupper hsupport.2
        refine ⟨q,⟨hInt.1,?_⟩,rfl⟩
        simpa only [H,add_assoc] using hInt.2
  calc
    _ ≤ sourceTransition hwn hell hS0 hS hr hs hsS mesh ((some h,Sum.inl z),flag)
        ((fun y => y.1.2) ⁻¹' (Sum.inl '' closedCostBin a (a+H))) := measure_mono_ae hdom
    _ = continuousChain (Real.log start.gap) ell S (.inl z) (Sum.inl '' closedCostBin a (a+H)) := by
      have hmR : Measurable (fun y : FlagState (JointState w ell S start) => y.1.2) :=
        measurable_snd.comp measurable_fst
      rw [← Measure.map_apply hmR hT,
        sourceTransition_right hwn hell hS0 hS hr hs hsS]
    _ ≤ ENNReal.ofReal (repeatDensityConstant*(1+(U+1))^2)*ENNReal.ofReal ((a+H)-a) :=
      (Classical.choose_spec completed_parent_interval_upper).2 _ _ _ _ _ _ z hzU
    _ = _ := by
      rw [add_sub_cancel_left,← ENNReal.ofReal_mul (mul_nonneg repeatDensityConstant_pos.le (sq_nonneg _))]
      congr 1
      unfold repeatBudget H
      ring
end NumberTheoryLean.RepeatedStepRowBound


end Erdos970

end OAI
