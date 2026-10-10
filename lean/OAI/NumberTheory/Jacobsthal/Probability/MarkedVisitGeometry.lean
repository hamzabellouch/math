import OAI.NumberTheory.Jacobsthal.Estimates.PairedBlockContraction

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedCostProcess

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open JointMinorization RegenerationTails PairedHitting

abbrev OddCost := OddState × ℝ

noncomputable def pairedDraws : Kernel OddState (EvenState × OddState) :=
  oddToEven ⊗ₖ evenToOdd.prodMkLeft OddState

instance pairedDraws_isMarkovKernel : IsMarkovKernel pairedDraws := by unfold pairedDraws; infer_instance

noncomputable def pairUpdate (x : OddCost × (EvenState × OddState)) : OddCost :=
  (x.2.2, x.1.2 + cost x.2.1.1 + cost x.2.2.1)

theorem pairUpdate_measurable : Measurable pairUpdate :=
  (measurable_snd.comp measurable_snd).prodMk
    (((measurable_snd.comp measurable_fst).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)))).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))))

noncomputable def pairedCostKernel : Kernel OddCost OddCost :=
  (Kernel.id ×ₖ pairedDraws.prodMkRight ℝ).map pairUpdate

instance pairedCostKernel_isMarkovKernel : IsMarkovKernel pairedCostKernel :=
  Kernel.IsMarkovKernel.map _ pairUpdate_measurable

theorem pairedCostKernel_apply (z : OddCost) {B : Set OddCost} (hB : MeasurableSet B) :
    pairedCostKernel z B = pairedDraws z.1 {x | (x.2, z.2 + cost x.1.1 + cost x.2.1) ∈ B} := by
  rw [pairedCostKernel, Kernel.map_apply' _ pairUpdate_measurable _ hB,
    Kernel.prod_apply' _ _ _ (pairUpdate_measurable hB), Kernel.id_apply, lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (pairUpdate_measurable hB)

theorem pairedCost_map_state (z : OddCost) : (pairedCostKernel z).map Prod.fst = pairedOdd z.1 := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB, pairedCostKernel_apply _ (measurable_fst hB),
    pairedOdd, Kernel.comp_eq_snd_compProd, Kernel.snd_apply' _ _ hB]
  rfl

theorem pairedCost_map_ratio_cost (z : OddCost) :
    (pairedCostKernel z).map (fun x => (x.1.1, x.2)) = oddJointKernel z.2 z.1 := by
  have hm : Measurable (fun x : OddCost => (x.1.1, x.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hp : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  ext B hB
  rw [Measure.map_apply hm hB, pairedCostKernel_apply _ (hm hB),
    oddJointKernel, Kernel.map_apply _ (pairCost_measurable z.2),
    Measure.map_apply (pairCost_measurable z.2) hB, oddTwoStep, Kernel.map_apply _ hp,
    Measure.map_apply hp ((pairCost_measurable z.2) hB)]
  rfl

theorem pairedDraws_regeneration (s : OddState) (hs : s.1 ≤ 3) :
    pairedDraws s = pairedDraws regenerationState := by
  have hf : oddToEven s = oddToEven regenerationState := by
    rw [oddToEven, Kernel.comapRight_apply, Kernel.comapRight_apply, oddKernel_regeneration s hs]
  ext B hB
  rw [pairedDraws, Kernel.compProd_apply hB, Kernel.compProd_apply hB]
  change (∫⁻ t : EvenState, evenToOdd t (Prod.mk t ⁻¹' B) ∂oddToEven s) =
    ∫⁻ t : EvenState, evenToOdd t (Prod.mk t ⁻¹' B) ∂oddToEven regenerationState
  rw [hf]

theorem pairedCost_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    pairedCostKernel (s, T) = pairedCostKernel (regenerationState, T) := by
  ext B hB
  rw [pairedCostKernel_apply _ hB, pairedCostKernel_apply _ hB]
  exact congrArg (fun μ : Measure (EvenState × OddState) =>
    μ {x | (x.2, T + cost x.1.1 + cost x.2.1) ∈ B}) (pairedDraws_regeneration s hs)

def shiftCost (T : ℝ) (z : OddCost) : OddCost := (z.1, z.2 + T)

theorem shiftCost_measurable (T : ℝ) : Measurable (shiftCost T) :=
  measurable_fst.prodMk (measurable_snd.add measurable_const)

theorem pairedCost_translation (s : OddState) (T a : ℝ) :
    (pairedCostKernel (s, T)).map (shiftCost a) = pairedCostKernel (s, T + a) := by
  ext B hB
  rw [Measure.map_apply (shiftCost_measurable a) hB,
    pairedCostKernel_apply _ ((shiftCost_measurable a) hB), pairedCostKernel_apply _ hB]
  congr 1
  ext x
  change (x.2, (T + cost x.1.1 + cost x.2.1) + a) ∈ B ↔
    (x.2, (T + a) + cost x.1.1 + cost x.2.1) ∈ B
  have heq : (T + cost x.1.1 + cost x.2.1) + a = (T + a) + cost x.1.1 + cost x.2.1 := by ring
  rw [heq]

end NumberTheoryLean.PairedCostProcess

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.RegenerationTails

noncomputable def sourceMark (t : EvenState) : Bool := if (209/100:ℝ) ≤ t.1 ∧ t.1 ≤ 213/100 then true else false

lemma sourceMark_measurable : Measurable sourceMark := by
  unfold sourceMark
  exact Measurable.ite (measurableSet_Icc.preimage measurable_subtype_coe) measurable_const measurable_const

abbrev MarkedOddCost := Bool × OddCost

noncomputable def markedPairUpdate (x : OddCost × (EvenState × OddState)) : MarkedOddCost :=
  (sourceMark x.2.1,pairUpdate x)

lemma markedPairUpdate_measurable : Measurable markedPairUpdate :=
  (sourceMark_measurable.comp (measurable_fst.comp measurable_snd)).prodMk pairUpdate_measurable

noncomputable def markedPairKernel : Kernel OddCost MarkedOddCost :=
  (Kernel.id ×ₖ pairedDraws.prodMkRight ℝ).map markedPairUpdate

instance markedPairKernel_isMarkovKernel : IsMarkovKernel markedPairKernel :=
  Kernel.IsMarkovKernel.map _ markedPairUpdate_measurable

lemma markedPairKernel_apply (z : OddCost) {B : Set MarkedOddCost} (hB : MeasurableSet B) :
    markedPairKernel z B = pairedDraws z.1
      {x | (sourceMark x.1,(x.2,z.2+cost x.1.1+cost x.2.1)) ∈ B} := by
  rw [markedPairKernel,Kernel.map_apply' _ markedPairUpdate_measurable _ hB,
    Kernel.prod_apply' _ _ _ (markedPairUpdate_measurable hB),Kernel.id_apply,lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (markedPairUpdate_measurable hB)

lemma markedPair_forget (z : OddCost) : (markedPairKernel z).map Prod.snd = pairedCostKernel z := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,markedPairKernel_apply _ (measurable_snd hB),
    pairedCostKernel_apply _ hB]
  rfl

lemma markedPair_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    markedPairKernel (s,T) = markedPairKernel (regenerationState,T) := by
  ext B hB
  rw [markedPairKernel_apply _ hB,markedPairKernel_apply _ hB,pairedDraws_regeneration s hs]

def markedShift (a : ℝ) (z : MarkedOddCost) : MarkedOddCost := (z.1,shiftCost a z.2)

lemma markedShift_measurable (a : ℝ) : Measurable (markedShift a) :=
  measurable_fst.prodMk ((shiftCost_measurable a).comp measurable_snd)

lemma markedPair_translation (s : OddState) (T a : ℝ) :
    (markedPairKernel (s,T)).map (markedShift a) = markedPairKernel (s,T+a) := by
  ext B hB
  rw [Measure.map_apply (markedShift_measurable a) hB,
    markedPairKernel_apply _ ((markedShift_measurable a) hB),markedPairKernel_apply _ hB]
  congr 1
  ext x
  change (sourceMark x.1,(x.2,(T+cost x.1.1+cost x.2.1)+a)) ∈ B ↔
    (sourceMark x.1,(x.2,(T+a)+cost x.1.1+cost x.2.1)) ∈ B
  rw [show (T+cost x.1.1+cost x.2.1)+a=(T+a)+cost x.1.1+cost x.2.1 by ring]

end Erdos970Dependency.MarkedVisits

end

section

namespace NumberTheoryLean.CostReturnLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels PairedHitting PairedBlockContraction PairedCostProcess

def returnSet : Set OddCost := Prod.fst ⁻¹' pairedRegeneration

theorem returnSet_measurable : MeasurableSet returnSet :=
  pairedRegeneration_measurable.preimage measurable_fst

noncomputable def costKilled : Kernel OddCost OddCost := pairedCostKernel.restrict returnSet_measurable.compl
noncomputable def costCaptured : Kernel OddCost OddCost := pairedCostKernel.restrict returnSet_measurable

instance costKilled_isFiniteKernel : IsFiniteKernel costKilled := by unfold costKilled; infer_instance
instance costCaptured_isFiniteKernel : IsFiniteKernel costCaptured := by unfold costCaptured; infer_instance

instance costKilled_pow_isFiniteKernel (n : ℕ) : IsFiniteKernel (costKilled ^ n) := by
  induction n with
  | zero => change IsFiniteKernel (Kernel.id : Kernel OddCost OddCost); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsFiniteKernel (costKilled ∘ₖ (costKilled ^ n))
    infer_instance

theorem costKilled_map_state (z : OddCost) : (costKilled z).map Prod.fst = pairedKilled z.1 := by
  rw [costKilled, Kernel.restrict_apply]
  change ((pairedCostKernel z).restrict (Prod.fst ⁻¹' pairedRegeneration)ᶜ).map Prod.fst = _
  rw [← preimage_compl, ← Measure.restrict_map measurable_fst pairedRegeneration_measurable.compl,
    pairedCost_map_state]
  rfl

theorem costKilled_pow_map_state (n : ℕ) (z : OddCost) :
    ((costKilled ^ n) z).map Prod.fst = (pairedKilled ^ n) z.1 := by
  induction n generalizing z with
  | zero =>
    change (Measure.dirac z).map Prod.fst = Measure.dirac z.1
    exact Measure.map_dirac' measurable_fst z
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro H hH
    rw [lintegral_map hH measurable_fst]
    have hp : costKilled ^ (n + 1) = (costKilled ^ n) ∘ₖ costKilled := pow_succ costKilled n
    have hq : pairedKilled ^ (n + 1) = (pairedKilled ^ n) ∘ₖ pairedKilled := pow_succ pairedKilled n
    rw [hp, hq, Kernel.lintegral_comp _ _ _ (g := fun z : OddCost => H z.1) (hH.comp measurable_fst),
      Kernel.lintegral_comp _ _ _ hH]
    have hi : ∀ y : OddCost, (∫⁻ w : OddCost, H w.1 ∂(costKilled ^ n) y) =
        ∫⁻ t, H t ∂(pairedKilled ^ n) y.1 := by
      intro y
      rw [← ih y, lintegral_map hH measurable_fst]
    simp_rw [hi]
    have hJ : Measurable (fun t : OddState => ∫⁻ u, H u ∂(pairedKilled ^ n) t) := hH.lintegral_kernel
    rw [← costKilled_map_state z, lintegral_map hJ measurable_fst]

theorem costKilled_mass (n : ℕ) (z : OddCost) :
    (costKilled ^ n) z univ = (pairedKilled ^ n) z.1 univ := by
  have h := congrArg (fun μ : Measure OddState => μ univ) (costKilled_pow_map_state n z)
  rwa [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at h

theorem cost_survival_tendsto_zero (z : OddCost) :
    Tendsto (fun n => (costKilled ^ n) z univ) atTop (𝓝 0) := by
  apply (paired_survival_tendsto_zero z.1).congr
  intro n
  exact (costKilled_mass n z).symm

noncomputable def firstReturn (n : ℕ) : Kernel OddCost OddCost := costCaptured ∘ₖ (costKilled ^ n)

instance firstReturn_isFiniteKernel (n : ℕ) : IsFiniteKernel (firstReturn n) := by unfold firstReturn; infer_instance

noncomputable def returnLaw : Kernel OddCost OddCost := Kernel.sum firstReturn

theorem costCaptured_add_costKilled : costCaptured + costKilled = pairedCostKernel := by
  ext z : 1
  change (pairedCostKernel z).restrict returnSet + (pairedCostKernel z).restrict returnSetᶜ = pairedCostKernel z
  exact Measure.restrict_add_restrict_compl returnSet_measurable

theorem return_mass_step (n : ℕ) (z : OddCost) :
    firstReturn n z univ + (costKilled ^ (n + 1)) z univ = (costKilled ^ n) z univ := by
  have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
  calc
    _ = ((costCaptured + costKilled) ∘ₖ (costKilled ^ n)) z univ := by
      rw [Kernel.comp_add_left, add_apply, Measure.add_apply, hp]
      rfl
    _ = (pairedCostKernel ∘ₖ (costKilled ^ n)) z univ := by rw [costCaptured_add_costKilled]
    _ = _ := by rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]; simp

theorem return_finite_mass (n : ℕ) (z : OddCost) :
    (costKilled ^ n) z univ + ∑ k ∈ Finset.range n, firstReturn k z univ = 1 := by
  induction n with
  | zero =>
    change (Measure.dirac z) univ + 0 = 1
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      _ = (∑ k ∈ Finset.range n, firstReturn k z univ) +
          (firstReturn n z univ + (costKilled ^ (n + 1)) z univ) := by ac_rfl
      _ = (∑ k ∈ Finset.range n, firstReturn k z univ) + (costKilled ^ n) z univ := by rw [return_mass_step]
      _ = 1 := by simpa only [add_comm] using ih

instance returnLaw_isMarkovKernel : IsMarkovKernel returnLaw := by
  constructor
  intro z
  constructor
  rw [returnLaw, Kernel.sum_apply' _ _ MeasurableSet.univ]
  have h := (cost_survival_tendsto_zero z).add (ENNReal.tendsto_nat_tsum (fun n => firstReturn n z univ))
  simp only [zero_add, return_finite_mass] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem costCaptured_off_returnSet (z : OddCost) : costCaptured z returnSetᶜ = 0 := by
  rw [costCaptured, Kernel.restrict_apply' _ _ _ returnSet_measurable.compl, compl_inter_self, measure_empty]

theorem firstReturn_off_returnSet (n : ℕ) (z : OddCost) : firstReturn n z returnSetᶜ = 0 := by
  rw [firstReturn, Kernel.comp_apply' _ _ _ returnSet_measurable.compl]
  simp only [costCaptured_off_returnSet, lintegral_zero]

theorem returnLaw_off_returnSet (z : OddCost) : returnLaw z returnSetᶜ = 0 := by
  rw [returnLaw, Kernel.sum_apply' _ _ returnSet_measurable.compl]
  simp only [firstReturn_off_returnSet, tsum_zero]

noncomputable def cycleCostLaw : Measure ℝ := (returnLaw (RegenerationTails.regenerationState, 0)).map Prod.snd

instance cycleCostLaw_isProbabilityMeasure : IsProbabilityMeasure cycleCostLaw :=
  (Measure.isProbabilityMeasure_map_iff (μ := returnLaw (RegenerationTails.regenerationState, 0))
    measurable_snd.aemeasurable).mpr inferInstance

end NumberTheoryLean.CostReturnLaw

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.RegenerationTails
open NumberTheoryLean.DerivativeWeights NumberTheoryLean.WeightFutureIntegrals
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.KernelDensityBridge

lemma regeneration_density_eq {t : ℝ} (ht : 2 ≤ t) :
    oddDensity regenerationState t = W t*phiEven t/phiOdd 1 := by
  simp [oddDensity,tailDensity,regenerationState,ht]

lemma regeneration_interval_positive {a b : ℝ} (ha : 2 ≤ a) (hab : a < b) :
    0 < oddKernel regenerationState (Icc a b) := by
  have hp : ∀ t ∈ Icc a b, 0 < oddDensity regenerationState t := by
    intro t ht
    rw [regeneration_density_eq (ha.trans ht.1)]
    exact div_pos (mul_pos (W_pos (by linarith [ht.1])) (phiEven_pos (by linarith [ht.1]))) (phiOdd_pos 1)
  have hf : ContinuousOn (fun t => W t*phiEven t/phiOdd 1) (Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht0
    have hW : ContinuousAt W t := by unfold W; fun_prop
    exact ((hW.mul (phiEven_continuousAt (by linarith [ht.1]))).div_const _).continuousWithinAt
  have hc : ContinuousOn (oddDensity regenerationState) (Icc a b) := hf.congr
    (fun t ht => regeneration_density_eq (ha.trans ht.1))
  have hi := intervalIntegral.integral_pos hab hc (fun t ht => (hp t ⟨ht.1.le,ht.2⟩).le)
    ⟨a,⟨le_rfl,hab.le⟩,hp a ⟨le_rfl,hab.le⟩⟩
  rw [oddKernel_apply,← ofReal_integral_eq_lintegral_ofReal
    (oddDensity_integrable regenerationState).integrableOn
    (Filter.Eventually.of_forall (oddDensity_nonneg regenerationState))]
  apply ENNReal.ofReal_pos.mpr
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab.le]
  exact hi

noncomputable def markProbability : ℝ≥0∞ :=
  oddKernel regenerationState (Icc (209/100:ℝ) (213/100))

lemma markProbability_pos : 0 < markProbability :=
  regeneration_interval_positive (by norm_num) (by norm_num)

lemma markProbability_lt_one : markProbability < 1 := by
  let J := Icc (5/2:ℝ) (13/5)
  have hJ : 0 < oddKernel regenerationState J := regeneration_interval_positive (by norm_num) (by norm_num)
  have hdisj : Disjoint (Icc (209/100:ℝ) (213/100)) J := by
    apply Set.disjoint_left.mpr
    intro t ht hj
    dsimp [J] at hj
    linarith [ht.2,hj.1]
  have hsum : markProbability+oddKernel regenerationState J ≤ 1 := by
    rw [markProbability,← measure_union hdisj measurableSet_Icc]
    exact prob_le_one
  exact (ENNReal.lt_add_right (measure_ne_top _ _) hJ.ne').trans_le hsum

lemma sourceMark_true (t : EvenState) : sourceMark t = true ↔ t.1 ∈ Icc (209/100:ℝ) (213/100) := by
  simp [sourceMark]

lemma markedPair_mark_mass (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    markedPairKernel (s,T) {z | z.1=true} = markProbability := by
  have hm : MeasurableSet {z : MarkedOddCost | z.1=true} := measurable_fst (measurableSet_singleton true)
  rw [markedPair_regeneration s hs T,markedPairKernel_apply _ hm]
  have he : {x : EvenState × OddState | sourceMark x.1=true} =
      Prod.fst ⁻¹' {t : EvenState | t.1 ∈ Icc (209/100:ℝ) (213/100)} := by
    ext x
    exact sourceMark_true x.1
  change pairedDraws regenerationState {x : EvenState × OddState | sourceMark x.1=true} = _
  rw [he]
  let E : Set EvenState := {t | t.1 ∈ Icc (209/100:ℝ) (213/100)}
  have hE : MeasurableSet E := measurable_subtype_coe measurableSet_Icc
  have hfst : pairedDraws.fst regenerationState E =
      pairedDraws regenerationState {p | p.1 ∈ E} := Kernel.fst_apply' _ _ hE
  change pairedDraws regenerationState {p | p.1 ∈ E} = _
  rw [← hfst,pairedDraws,Kernel.fst_compProd]
  have hmap := oddToEven_map_ratio regenerationState
  have hmeasure := congrArg (fun μ : Measure ℝ => μ (Icc (209/100:ℝ) (213/100))) hmap
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc] at hmeasure
  exact hmeasure

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set
open scoped Topology
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry

noncomputable def gapAt (r T : ℝ) : ℝ := r*Real.exp (-T)

lemma gapAt_pathCost {i : Side} {s r : ℝ} {ts : List ℝ}
    (hs : Valid i s) (ht : Admissible i s ts) : gapAt r (pathCost ts) = finalGap r ts :=
  (finalGap_eq_cost hs ht).symm

lemma nextExponent_scale (a r t : ℝ) : nextExponent (a*r) t = a*nextExponent r t := by
  unfold nextExponent
  ring

lemma nextGap_scale (a r t : ℝ) : nextGap (a*r) t = a*nextGap r t := by
  unfold nextGap
  ring

lemma marked_draw_slack {b0 b1 r t : ℝ} (hb0 : 0 < b0)
    (hr0 : 10*b0 ≤ r) (hr1 : r ≤ b1) (ht0 : 209/100 ≤ t) (ht1 : t ≤ 213/100) :
    10*b0/(313/100) ≤ nextExponent r t ∧ nextExponent r t ≤ b1/(309/100) ∧
    2*b0 ≤ nextExponent r t ∧ nextExponent r t ≤ b1/2 ∧
    6*b0 < nextGap r t ∧ nextGap r t/nextExponent r t=t := by
  have hr : 0 < r := by linarith
  have ht : 0 < t := by linarith
  have htp : 0 < t+1 := by linarith
  have hlow : 10*b0/(313/100) ≤ nextExponent r t := by
    unfold nextExponent
    exact div_le_div₀ (by positivity) hr0 htp (by linarith)
  have hhi : nextExponent r t ≤ b1/(309/100) := by
    unfold nextExponent
    exact div_le_div₀ (hr.le.trans hr1) hr1 (by norm_num) (by linarith)
  have hlo2 : 2*b0 ≤ nextExponent r t := by
    apply (le_div_iff₀ htp).mpr
    nlinarith
  have hhi2 : nextExponent r t ≤ b1/2 := by
    unfold nextExponent
    exact div_le_div₀ (hr.le.trans hr1) hr1 (by norm_num) (by linarith)
  have hgap : 6*b0 < nextGap r t := by
    unfold nextGap
    apply (lt_div_iff₀ htp).mpr
    have hm := mul_le_mul_of_nonneg_right hr0 ht.le
    nlinarith
  exact ⟨hlow,hhi,hlo2,hhi2,hgap,nextRatio_identity hr ht⟩

lemma gapAt_le_iff {r B : ℝ} (hr : 0 < r) (hB : 0 < B) (T : ℝ) :
    gapAt r T ≤ B ↔ Real.log (r/B) ≤ T := by
  rw [gapAt,Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos T),
    Real.log_le_iff_le_exp (div_pos hr hB),div_le_iff₀ hB]
  simp only [mul_comm]

lemma le_gapAt_iff {r A : ℝ} (hr : 0 < r) (hA : 0 < A) (T : ℝ) :
    A ≤ gapAt r T ↔ T ≤ Real.log (r/A) := by
  rw [gapAt,Real.exp_neg,← div_eq_mul_inv,le_div_iff₀ (Real.exp_pos T),
    Real.le_log_iff_exp_le (div_pos hr hA),le_div_iff₀ hA]
  simp only [mul_comm]

lemma marked_cost_window {r b0 b1 : ℝ} (hr : 0 < r) (hb0 : 0 < b0) (hb1 : 0 < b1) (T : ℝ) :
    10*b0 ≤ gapAt r T ∧ gapAt r T ≤ b1 ↔
      Real.log (r/b1) ≤ T ∧ T ≤ Real.log (r/b1)+Real.log (b1/(10*b0)) := by
  have he : Real.log (r/(10*b0)) = Real.log (r/b1)+Real.log (b1/(10*b0)) := by
    rw [Real.log_div hr.ne' (by positivity),Real.log_div hr.ne' hb1.ne',
      Real.log_div hb1.ne' (by positivity)]
    ring
  rw [le_gapAt_iff hr (by positivity),gapAt_le_iff hr hb1,he,and_comm]

lemma proportional_window_width {rho b0 : ℝ} (hrho : 0 < rho) (hb0 : 0 < b0) :
    Real.log ((rho*b0)/(10*b0)) = Real.log (rho/10) := by
  congr 1
  field_simp

lemma moving_window_cost_threshold {K rho : ℝ} (hK : 0 < K) (hrho : 0 < rho) (M : ℝ) :
    ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r →
      M ≤ Real.log (r/(rho*K*(Real.log w)^2)) := by
  have ht : Tendsto (fun w:ℝ => (Real.log w)^2/w) atTop (𝓝 0) := by
    simpa only [one_mul,add_zero] using Real.tendsto_pow_log_div_mul_add_atTop (1:ℝ) 0 2 one_ne_zero
  have hl : Tendsto (fun w:ℝ => (Real.exp M*rho*K)*((Real.log w)^2/w)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul (Real.exp M*rho*K)
  filter_upwards [eventually_ge_atTop (3:ℝ),hl.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with w hw hs
  refine ⟨hw,?_⟩
  intro r hr
  have hw0 : 0 < w := by linarith
  have hr0 : 0 < r := hw0.trans_le hr
  have hlog : 0 < Real.log w := Real.log_pos (by linarith)
  have hden : 0 < rho*K*(Real.log w)^2 := by positivity
  apply (Real.le_log_iff_exp_le (div_pos hr0 hden)).mpr
  apply (le_div_iff₀ hden).mpr
  have he := (div_le_iff₀ hw0).mp (show (Real.exp M*rho*K*(Real.log w)^2)/w ≤ 1 by simpa only [mul_div_assoc] using hs.le)
  nlinarith

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
