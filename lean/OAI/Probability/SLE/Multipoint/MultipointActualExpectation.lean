import OAI.Probability.SLE.Multipoint.MultipointActualPhases
import OAI.Probability.SLE.Multipoint.MultipointLocalizedExpectation
import OAI.Probability.SLE.Multipoint.MultipointSelectedRate
import OAI.Probability.SLE.Multipoint.MultipointStateBounds
import OAI.Probability.SLE.Multipoint.MultipointTerminalProbability

namespace OAI

/-! The actual localized multipoint product has expectation at most one.
The bounded discount process is constructed, not supplied as an input. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem actual_localized_product_expectation
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ β lo hi M : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    {H : ℝ≥0} (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane)
    (u₀ u₂ : ι → ℝ) (h₀ : ∀ i, 0 ≤ u₀ i) (hu : ∀ i, u₀ i ≤ u₂ i)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (S : LocalizedState B hm κ lo hi M H z
      (fun i => actualFactorStops γ G z u₀ u₂ H (i,2)) γ G) :
    let ρ := actualFactorStops γ G z u₀ u₂ H
    let a := fun i => sourceClockLevel κ (z i) (u₀ i)
    let U := fun i => κ/4*(u₂ i-u₀ i)
    ∃ (r : ℝ≥0 → Ω → ℝ) (C : ℝ≥0),
      Measurable (Function.uncurry r) ∧
      IsProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) r ∧
      (∀ t ω, 0 ≤ r t ω ∧ |r t ω| ≤ C) ∧
      (∀ ω t, t < S.χ ω → r t ω =
        productDriftCost (patternActiveSet (phaseAt ρ t ω)) κ
          (fun i => phaseRegulatorScale β (a i) (U i) (phaseAt ρ t ω i))
          (fun i => phaseRegulatorSlope β (phaseAt ρ t ω i)) (S.Q t ω) (B t ω)) ∧
      Integrable (fun ω => discountedPatternProduct κ β a U (phaseAt ρ (S.χ ω) ω)
        (S.Q (S.χ ω) ω,discountClock r (S.χ ω) ω) (B (S.χ ω) ω)) P ∧
      (∫ ω, discountedPatternProduct κ β a U (phaseAt ρ (S.χ ω) ω)
        (S.Q (S.χ ω) ω,discountClock r (S.χ ω) ω) (B (S.χ ω) ω) ∂P) ≤ 1 := by
  classical
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  dsimp only
  let ρ := actualFactorStops γ G z u₀ u₂ H
  let a := fun i => sourceClockLevel κ (z i) (u₀ i)
  let U := fun i => κ/4*(u₂ i-u₀ i)
  let l := factorSwitchList ρ
  obtain ⟨hρstop,horder,hρbound⟩ := actualFactorStops_regular hB hm hBm hBc hB0
    κ hκ hκ8 γ G F hw z hz u₀ u₂ h₀ hu H
  have hlstop := factorSwitchList_forall ρ
    (fun τ => IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (by
      simpa only [WithTop.coe_zero] using
        (isStoppingTime_const (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
          (0 : ℝ≥0))) hρstop
  have hlbound := factorSwitchList_forall ρ (fun τ => ∀ ω, τ ω ≤ H+1)
    (fun _ => bot_le) hρbound
  have hU (i : ι) : 0 ≤ U i := mul_nonneg (div_nonneg hκ.le (by norm_num)) (sub_nonneg.mpr (hu i))
  let q₀ := fun i => initialLogCoordinates (z i)
  have hQ0 (ω : Ω) : S.Q 0 ω = q₀ := funext (S.initial ω)
  let Qbound := ‖q₀‖+(S.L : ℝ)*(H : ℝ)
  have hQbound (ω : Ω) (t : ℝ≥0) (ht : t ≤ S.χ ω) : ‖S.Q t ω‖ ≤ Qbound := by
    have hh := lipschitz_state_norm_le (fun u => S.Q u ω) S.L (S.lipschitz ω)
      H t t.coe_nonneg (by exact_mod_cast ht.trans (S.bounded ω))
    simpa only [hQ0 ω] using hh
  let R₀ := max Qbound M
  have hR₀ : 0 ≤ R₀ := (by positivity : (0 : ℝ) ≤ Qbound).trans (le_max_left _ _)
  have hnorm₀ (ω : Ω) (t : ℝ≥0) (ht : t ≤ S.χ ω) : ‖(S.Q t ω,B t ω)‖ ≤ R₀ := by
    rw [Prod.norm_def,Real.norm_eq_abs]
    exact max_le_max (hQbound ω t ht) (S.driver_bound ω t ht)
  obtain ⟨r,C,hrm,hrp,hrb,hcost⟩ := exists_localized_discount_rate B hm hBm hBc
    S.Q S.measurable S.adapted (fun ω => (S.lipschitz ω).continuous) κ β hκ hκ8 a U
    ρ l H hlstop hlbound (factorSwitchList_mem ρ) (factorSwitchList_zero ρ)
    S.χ S.stopping S.bounded R₀ hR₀ hnorm₀
  have hrt (ω : Ω) : Measurable (fun t => r t ω) :=
    hrm.comp (measurable_id.prodMk measurable_const)
  let R := max (max Qbound ((C : ℝ)*(H : ℝ))) M
  have hR : 0 ≤ R := (by positivity : (0 : ℝ) ≤ Qbound).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  have hnorm (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (htχ : t ≤ (S.χ ω : ℝ)) :
      ‖((S.Q t ω,discountClock r t ω),B t.toNNReal ω)‖ ≤ R :=
    discounted_state_norm_bound S.Q S.L S.lipschitz q₀ hQ0 r hrt C
      (fun t ω => (hrb t ω).2) B S.χ H S.bounded M
      (fun ω t ht => by simpa only [Real.norm_eq_abs] using S.driver_bound ω t ht) ω t ht htχ
  have hclock (ω : Ω) (i : ι) (k : Fin 3) (hk : ρ (i,k) ω ≤ S.χ ω) :
      logFactorClock κ (S.Q (ρ (i,k) ω) ω i)-a i =
        if k = 0 then 0 else if k = 1 then U i/2 else U i :=
    actual_phase_switch_clock hBc hκ hw S horder ω i k hk
  obtain ⟨hI,hmean⟩ := localized_pattern_expectation_le hB hm hBm hBc S.Q S.V S.L
    S.measurable S.adapted S.lipschitz S.velocity_measurable S.velocity_bound S.derivative
    r hrm hrp C (fun t ω => (hrb t ω).2) κ β hκ hκ8 hβ hβ1 a U hU ρ l H
    hlstop hlbound (factorSwitchList_mem ρ) horder (factorSwitchList_zero ρ)
    S.χ S.stopping S.bounded R hR hnorm
    (fun ω t ht i hi => (actual_phase_regulator hBc hκ hβ h₀ hu hw S horder ω t ht.le i
      (Finset.mem_filter.mp hi).2).2)
    (fun ω t ht i hi => S.physical_velocity ω t ht i
      ((phaseAt_active_iff ρ ω i (horder ω i) t).mp (Finset.mem_filter.mp hi).2).2)
    hcost hclock
  refine ⟨r,C,hrm,hrp,hrb,hcost,hI,hmean.trans ?_⟩
  have hinit (ω : Ω) : discountedPatternProduct κ β a U (phaseAt ρ 0 ω)
      (S.Q 0 ω,discountClock r 0 ω) (B 0 ω) ≤ 1 := by
    simp only [discountedPatternProduct, discountClock_initial, neg_zero, Real.exp_zero, one_mul]
    apply initial_phase_product_le_one κ β hκ hκ8 a U hU ρ ω (horder ω) (S.Q 0 ω) (B 0 ω)
    intro i k hk
    have hh := hclock ω i k (by rw [hk]; exact bot_le)
    simpa only [hk, NNReal.coe_zero] using hh
  have hnonneg (ω : Ω) : 0 ≤ discountedPatternProduct κ β a U (phaseAt ρ 0 ω)
      (S.Q 0 ω,discountClock r 0 ω) (B 0 ω) :=
    mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun i _ =>
      (phaseFactor_pos κ β (a i) (U i) (phaseAt ρ 0 ω i) (S.Q 0 ω i) (B 0 ω)).le))
  simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono_of_nonneg (μ := P) (ae_of_all P hnonneg)
      (integrable_const (1 : ℝ)) (ae_of_all P hinit)

end SLEExactGauge.Multipoint

end

end OAI
