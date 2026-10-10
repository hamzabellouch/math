import OAI.NumberTheory.Jacobsthal.Primes.PrimeGridGeometry
import OAI.NumberTheory.Jacobsthal.Probability.CemeteryHistoryLaw

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ContinuousRatioBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry TransitionKernels PrimeTiltBounds PrimeTiltMonotone
open PrimeRatioMeasure HarmonicExponentMeasure

noncomputable def weightedRatioLaw (i : Side) (s : ℝ) : Measure ℝ :=
  (ratioMeasure (minRatio i s)).withDensity (fun t => ENNReal.ofReal (multiplier i s t))

theorem weightedRatioLaw_eq_density {i : Side} {s : ℝ} (hs : Valid i s) :
    weightedRatioLaw i s = volume.withDensity (fun t => ENNReal.ofReal (transitionDensity i s t)) := by
  unfold weightedRatioLaw ratioMeasure
  rw [← withDensity_mul _ (f := fun t : ℝ => ENNReal.ofReal (1/(t+1)))
    (g := fun t : ℝ => ENNReal.ofReal (multiplier i s t))
    (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (1/(t+1))))
    (ENNReal.measurable_ofReal.comp (multiplier_measurable i s)), ← withDensity_indicator measurableSet_Ici]
  apply congrArg (fun f : ℝ → ℝ≥0∞ => volume.withDensity f)
  funext t
  exact weighted_ratio_density_eq hs t

theorem weightedRatioLaw_probability {i : Side} {s : ℝ} (hs : Valid i s) :
    IsProbabilityMeasure (weightedRatioLaw i s) := by
  constructor
  rw [weightedRatioLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, multiplier_ratio_integral hs]

theorem weightedRatioLaw_even (s : EvenState) : weightedRatioLaw .even s.1 = evenKernel s := by
  apply Measure.ext
  intro B hB
  rw [weightedRatioLaw_eq_density (i := .even) (s := s.1) s.2, withDensity_apply _ hB, evenKernel_apply]
  rfl

theorem weightedRatioLaw_odd (s : OddState) : weightedRatioLaw .odd s.1 = oddKernel s := by
  apply Measure.ext
  intro B hB
  rw [weightedRatioLaw_eq_density (i := .odd) (s := s.1) s.2, withDensity_apply _ hB, oddKernel_apply]
  rfl

instance ratioMeasure_noAtoms (a : ℝ) : NullSingletonClass (ratioMeasure a) := by
  unfold ratioMeasure
  infer_instance

theorem ratio_restrict_bin {m a b : ℝ} (hma : m ≤ a) :
    (ratioMeasure m).restrict (Ico a b) = (ratioMeasure a).restrict (Ico a b) := by
  simp only [ratioMeasure, restrict_withDensity measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico]
  rw [Set.inter_eq_left.mpr (show Ico a b ⊆ Ici m from fun _ ht => hma.trans ht.1),
    Set.inter_eq_left.mpr Ico_subset_Ici_self]

theorem ratio_bin_mass {m a b : ℝ} (ha : 0 < a) (hma : m ≤ a) (hab : a ≤ b) :
    ratioMeasure m (Ico a b) = ENNReal.ofReal (Real.log (b+1)-Real.log (a+1)) := by
  have h := congrArg (fun μ : Measure ℝ => μ univ) (ratio_restrict_bin (b := b) hma)
  simp only [Measure.restrict_apply_univ] at h
  rw [h]
  have h' := congrArg (fun μ : Measure ℝ => μ univ)
    (restrict_Ico_eq_restrict_Icc (μ := ratioMeasure a) (a := a) (b := b))
  simp only [Measure.restrict_apply_univ] at h'
  rw [h', ratioMeasure_Icc ha hab]

noncomputable def continuousBin (i : Side) (s a b : ℝ) : ℝ :=
  (weightedRatioLaw i s (Ico a b)).toReal

theorem continuousBin_sandwich {i : Side} {s a b : ℝ} (hs : Valid i s)
    (hma : minRatio i s ≤ a) (hab : a ≤ b) :
    multiplier i s b * (Real.log (b+1)-Real.log (a+1)) ≤ continuousBin i s a b ∧
      continuousBin i s a b ≤ multiplier i s a * (Real.log (b+1)-Real.log (a+1)) := by
  let := weightedRatioLaw_probability hs
  have ha := (minRatio_pos hs).trans_le hma
  have hb := ha.trans_le hab
  have hma0 := (multiplier_pos hs (valid_next hs hma)).le
  have hmb0 := (multiplier_pos hs (valid_next hs (hma.trans hab))).le
  have hH : 0 ≤ Real.log (b+1)-Real.log (a+1) :=
    sub_nonneg.mpr (Real.log_le_log (by linarith) (by linarith))
  have hfinite : weightedRatioLaw i s (Ico a b) ≠ ∞ := measure_ne_top _ _
  have hu : weightedRatioLaw i s (Ico a b) ≤
      ENNReal.ofReal (multiplier i s a * (Real.log (b+1)-Real.log (a+1))) := by
    rw [weightedRatioLaw, withDensity_apply _ measurableSet_Ico]
    calc
      _ ≤ ∫⁻ _t in Ico a b, ENNReal.ofReal (multiplier i s a) ∂ratioMeasure (minRatio i s) := by
        apply lintegral_mono_ae
        apply ae_restrict_of_forall_mem measurableSet_Ico
        intro t ht
        exact ENNReal.ofReal_le_ofReal (multiplier_antitone hs (Set.mem_Ici.mpr hma)
          (Set.mem_Ici.mpr (hma.trans ht.1)) ht.1)
      _ = _ := by
        rw [lintegral_const, Measure.restrict_apply_univ, ratio_bin_mass ha hma hab,
          ← ENNReal.ofReal_mul hma0]
  have hl : ENNReal.ofReal (multiplier i s b * (Real.log (b+1)-Real.log (a+1))) ≤
      weightedRatioLaw i s (Ico a b) := by
    rw [weightedRatioLaw, withDensity_apply _ measurableSet_Ico]
    calc
      _ = ∫⁻ _t in Ico a b, ENNReal.ofReal (multiplier i s b) ∂ratioMeasure (minRatio i s) := by
        rw [lintegral_const, Measure.restrict_apply_univ, ratio_bin_mass ha hma hab,
          ← ENNReal.ofReal_mul hmb0]
      _ ≤ _ := by
        apply lintegral_mono_ae
        apply ae_restrict_of_forall_mem measurableSet_Ico
        intro t ht
        exact ENNReal.ofReal_le_ofReal (multiplier_antitone hs
          (Set.mem_Ici.mpr (hma.trans ht.1)) (Set.mem_Ici.mpr (hma.trans hab)) ht.2.le)
  constructor
  · have h := ENNReal.toReal_mono hfinite hl
    simpa only [continuousBin, ENNReal.toReal_ofReal (mul_nonneg hmb0 hH)] using h
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
    simpa only [continuousBin, ENNReal.toReal_ofReal (mul_nonneg hma0 hH)] using h

end NumberTheoryLean.ContinuousRatioBins

end

section

namespace NumberTheoryLean.ContinuousKilledBins

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PairedCostGrouping ArrivalKernelGeometry
open LowStateHorizon RegeneratingInverseBands KernelDensityBridge ContinuousRatioBins

noncomputable def continuousChain (v ell S : ℝ) : Kernel (CemeteryKernel.Space CostState) (CemeteryKernel.Space CostState) :=
  CemeteryKernel.complete (lowKernel costKernel v ell S)

instance continuousChain_isMarkov (v ell S : ℝ) : IsMarkovKernel (continuousChain v ell S) := by
  apply CemeteryKernel.complete_isMarkov
  intro z
  rw [lowKernel, Kernel.restrict_apply, Measure.restrict_apply_univ]
  calc
    _ ≤ costKernel z univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

def ratioBinSet (a b : ℝ) : Set CostState := {z | a ≤ stateRatio z.1 ∧ stateRatio z.1 < b}

theorem ratioBinSet_measurable (a b : ℝ) : MeasurableSet (ratioBinSet a b) :=
  (measurableSet_le measurable_const (stateRatio_measurable.comp measurable_fst)).inter
    (measurableSet_lt (stateRatio_measurable.comp measurable_fst) measurable_const)

theorem costKernel_ratioLaw (z : CostState) :
    (costKernel z).map (fun y : CostState => stateRatio y.1) = weightedRatioLaw (stateSide z.1) (stateRatio z.1) := by
  have hU : Measurable (fun s : State => (s,z.2+cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, Measure.map_map (g := fun y : CostState => stateRatio y.1)
    (stateRatio_measurable.comp measurable_fst) hU]
  change (stateKernel z.1).map stateRatio = _
  rcases z with ⟨s,T⟩
  cases s with
  | inl s =>
    rw [stateKernel_even_ratio]
    exact (weightedRatioLaw_even s).symm
  | inr s =>
    rw [stateKernel_odd_ratio]
    exact (weightedRatioLaw_odd s).symm

theorem costKernel_bin (z : CostState) (a b : ℝ) :
    costKernel z (ratioBinSet a b) = weightedRatioLaw (stateSide z.1) (stateRatio z.1) (Ico a b) := by
  have h := congrArg (fun μ : Measure ℝ => μ (Ico a b)) (costKernel_ratioLaw z)
  rw [Measure.map_apply (f := fun y : CostState => stateRatio y.1) (stateRatio_measurable.comp measurable_fst) measurableSet_Ico] at h
  exact h

theorem lowKernel_full_bin (v : ℝ) {ell S a b : ℝ} (hell : 0 < ell) (z : CostState)
    (hbS : b ≤ S) (harr : b ≤ gapValue v z/ell-1) :
    lowKernel costKernel v ell S z (ratioBinSet a b) = costKernel z (ratioBinSet a b) := by
  rw [lowKernel, Kernel.restrict_apply, Measure.restrict_apply (ratioBinSet_measurable a b)]
  apply measure_congr
  filter_upwards [costKernel_time_update z] with y hy
  apply propext
  constructor
  · exact And.left
  · intro hbin
    refine ⟨hbin,?_,?_⟩
    · have ht := OccupationBoundaries.stateRatio_pos y.1
      have hpair : y = (y.1,z.2+cost (stateRatio y.1)) := Prod.ext rfl hy
      have hcur : currentExponent v y = nextExponent (gapValue v z) (stateRatio y.1) := by
        calc
          _ = currentExponent v (y.1,z.2+cost (stateRatio y.1)) := congrArg (currentExponent v) hpair
          _ = _ := currentExponent_update v z y.1
      change ell < currentExponent v y
      rw [hcur]
      change ell < gapValue v z/(stateRatio y.1+1)
      apply (lt_div_iff₀ (by linarith : 0 < stateRatio y.1+1)).mpr
      have hratio : stateRatio y.1+1 < gapValue v z/ell := by
        change a ≤ stateRatio y.1 ∧ stateRatio y.1 < b at hbin
        linarith [hbin.2]
      have hm := (lt_div_iff₀ hell).mp hratio
      nlinarith
    · exact hbin.2.le.trans hbS

theorem continuousChain_full_bin (v : ℝ) {ell S a b : ℝ} (hell : 0 < ell) (z : CostState)
    (hbS : b ≤ S) (harr : b ≤ gapValue v z/ell-1) :
    continuousChain v ell S (.inl z) (Sum.inl '' ratioBinSet a b) =
      weightedRatioLaw (stateSide z.1) (stateRatio z.1) (Ico a b) := by
  rw [continuousChain, CemeteryKernel.complete_live_mass _ _ (ratioBinSet_measurable a b),
    lowKernel_full_bin v hell z hbS harr, costKernel_bin]

theorem continuousChain_full_bin_real (v : ℝ) {ell S a b : ℝ} (hell : 0 < ell) (z : CostState)
    (hbS : b ≤ S) (harr : b ≤ gapValue v z/ell-1) :
    (continuousChain v ell S (.inl z) (Sum.inl '' ratioBinSet a b)).toReal =
      continuousBin (stateSide z.1) (stateRatio z.1) a b := by
  rw [continuousChain_full_bin v hell z hbS harr]
  rfl

end NumberTheoryLean.ContinuousKilledBins

end

section

namespace NumberTheoryLean.ContinuousIntervalUpper

open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeTiltBounds PrimeTiltMonotone
open ContinuousRatioBins ContinuousKilledBins LowStateHorizon

theorem transition_density_upper : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, ∀ i : Side, ∀ s : ℝ,
    Valid i s → s ≤ S → ∀ t : ℝ,
      ENNReal.ofReal (transitionDensity i s t) ≤ ENNReal.ofReal (C*(1+S)^2) := by
  obtain ⟨C,hC,henv⟩ := multiplier_envelope
  refine ⟨C,hC,?_⟩
  intro S i s hs hsS t
  rw [← weighted_ratio_density_eq hs t]
  by_cases ht : minRatio i s ≤ t
  · rw [indicator_of_mem (show t ∈ Ici (minRatio i s) from ht)]
    have ht0 := valid_pos (valid_next hs ht)
    have hinv : ENNReal.ofReal (1/(t+1)) ≤ 1 := by
      apply (ENNReal.ofReal_le_one).mpr
      exact (div_le_iff₀ (by linarith : 0 < t+1)).mpr (by linarith)
    calc
      _ ≤ 1*ENNReal.ofReal (C*(1+S)^2) := mul_le_mul hinv (ENNReal.ofReal_le_ofReal (henv S i s t hs hsS ht)) zero_le zero_le
      _ = _ := one_mul _
  · rw [indicator_of_notMem (show t ∉ Ici (minRatio i s) from ht)]
    exact zero_le

theorem weighted_interval_upper : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, ∀ i : Side, ∀ s a b : ℝ,
    Valid i s → s ≤ S →
      weightedRatioLaw i s (Icc a b) ≤ ENNReal.ofReal (C*(1+S)^2) * ENNReal.ofReal (b-a) := by
  obtain ⟨C,hC,hbound⟩ := transition_density_upper
  refine ⟨C,hC,?_⟩
  intro S i s a b hs hsS
  rw [weightedRatioLaw_eq_density hs,withDensity_apply _ measurableSet_Icc]
  calc
    _ ≤ ∫⁻ _t in Icc a b, ENNReal.ofReal (C*(1+S)^2) := lintegral_mono (hbound S i s hs hsS)
    _ = _ := by rw [setLIntegral_const,Real.volume_Icc]

def closedCostBin (a b : ℝ) : Set CostState :=
  {z | a ≤ stateRatio z.1 ∧ stateRatio z.1 ≤ b}

theorem closedCostBin_measurable (a b : ℝ) : MeasurableSet (closedCostBin a b) :=
  (stateRatio_measurable.comp measurable_fst) measurableSet_Icc

theorem costKernel_closedBin (z : CostState) (a b : ℝ) :
    costKernel z (closedCostBin a b) = weightedRatioLaw (stateSide z.1) (stateRatio z.1) (Icc a b) := by
  have h := congrArg (fun μ : Measure ℝ => μ (Icc a b)) (costKernel_ratioLaw z)
  rw [Measure.map_apply (f := fun y : CostState => stateRatio y.1) (stateRatio_measurable.comp measurable_fst) measurableSet_Icc] at h
  exact h

theorem completed_interval_upper : ∃ C : ℝ, 0 < C ∧ ∀ v ell S a b : ℝ, ∀ z : CostState,
    stateRatio z.1 ≤ S →
      continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin a b) ≤
        ENNReal.ofReal (C*(1+S)^2) * ENNReal.ofReal (b-a) := by
  obtain ⟨C,hC,hbound⟩ := weighted_interval_upper
  refine ⟨C,hC,?_⟩
  intro v ell S a b z hsS
  rw [continuousChain,CemeteryKernel.complete_live_mass _ _ (closedCostBin_measurable a b),
    lowKernel,Kernel.restrict_apply,Measure.restrict_apply (closedCostBin_measurable a b)]
  calc
    _ ≤ costKernel z (closedCostBin a b) := measure_mono inter_subset_left
    _ = weightedRatioLaw (stateSide z.1) (stateRatio z.1) (Icc a b) := costKernel_closedBin z a b
    _ ≤ _ := hbound S (stateSide z.1) (stateRatio z.1) a b (stateRatio_valid z.1) hsS

end NumberTheoryLean.ContinuousIntervalUpper

end

section

namespace NumberTheoryLean.CompletedParentInterval
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures ContinuousIntervalUpper ContinuousRatioBins ContinuousKilledBins LowStateHorizon

theorem completed_parent_interval_upper : ∃ C : ℝ,0 < C ∧
    ∀ v ell S U a b : ℝ,∀ z : CostState,stateRatio z.1 ≤ U →
      continuousChain v ell S (.inl z) (Sum.inl '' closedCostBin a b) ≤
        ENNReal.ofReal (C*(1+U)^2)*ENNReal.ofReal (b-a) := by
  obtain ⟨C,hC,hbound⟩ := weighted_interval_upper
  refine ⟨C,hC,?_⟩
  intro v ell S U a b z hz
  rw [continuousChain,CemeteryKernel.complete_live_mass _ _ (closedCostBin_measurable a b),
    lowKernel,Kernel.restrict_apply,Measure.restrict_apply (closedCostBin_measurable a b)]
  calc
    _ ≤ costKernel z (closedCostBin a b) := measure_mono inter_subset_left
    _ = _ := costKernel_closedBin z a b
    _ ≤ _ := hbound U (stateSide z.1) (stateRatio z.1) a b (stateRatio_valid z.1) hz
end NumberTheoryLean.CompletedParentInterval

end

end Erdos970

end OAI
