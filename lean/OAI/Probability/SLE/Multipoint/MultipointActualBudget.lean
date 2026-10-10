import OAI.Probability.SLE.Multipoint.MultipointActualExpectation
import OAI.Probability.SLE.Multipoint.MultipointCostAssembly
import OAI.Probability.SLE.Multipoint.MultipointInitialParameters

namespace OAI

/-! The uniform discount budget for the actual, individually stopped
Loewner coordinates in an arbitrary conformal image. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem actual_localized_discount_le
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    {κ β lo hi M : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hβ : 0 < β)
    (hdecay : 2*(exponent (greenExponent κ)*β) < 2/κ)
    {H : ℝ≥0} (z : ι → ℂ) (hne : Function.Injective z)
    (u₀ u₂ : ι → ℝ) (h₀ : ∀ i, 0 ≤ u₀ i) (hu : ∀ i, u₀ i ≤ u₂ i)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (S : LocalizedState B hm κ lo hi M H z
      (fun i => actualFactorStops γ G z u₀ u₂ H (i,2)) γ G)
    (horder : ∀ ω i, Monotone (fun k => actualFactorStops γ G z u₀ u₂ H (i,k) ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (J : ℂ → ℂ)
    (hJ : DifferentiableOn ℂ J upperHalfPlane) (hJinj : InjOn J upperHalfPlane)
    (R b : ι → ℝ) (hR : ∀ i, 0 < R i) (hb : ∀ i, 0 < b i)
    (hRdef : ∀ i, R i = 2*(z i).im*‖deriv J (z i)‖)
    (hu₀ : ∀ i, u₀ i = Real.log (R i/b i))
    (hsep : ∀ i j, i ≠ j → b i ≤ dist (J (z i)) (J (z j)))
    (r : ℝ≥0 → Ω → ℝ) (C : ℝ≥0)
    (hrm : Measurable (Function.uncurry r)) (hrb : ∀ t ω, |r t ω| ≤ C)
    (hcost : ∀ ω t, t < S.χ ω → r t ω =
      productDriftCost (patternActiveSet (phaseAt (actualFactorStops γ G z u₀ u₂ H) t ω)) κ
        (fun i => phaseRegulatorScale β (sourceClockLevel κ (z i) (u₀ i))
          (κ/4*(u₂ i-u₀ i)) (phaseAt (actualFactorStops γ G z u₀ u₂ H) t ω i))
        (fun i => phaseRegulatorSlope β (phaseAt (actualFactorStops γ G z u₀ u₂ H) t ω i))
        (S.Q t ω) (B t ω)) (ω : Ω) :
    discountClock r (S.χ ω) ω ≤ uniformDiscountBudget κ β (Finset.univ : Finset ι) := by
  classical
  let ρ := actualFactorStops γ G z u₀ u₂ H
  let a := fun i => sourceClockLevel κ (z i) (u₀ i)
  let U := fun i => κ/4*(u₂ i-u₀ i)
  let σ := fun i => min (ρ (i,0) ω) (S.χ ω)
  let T := fun i => min (ρ (i,2) ω) (S.χ ω)
  have hσT (i : ι) : σ i ≤ T i := min_le_min (horder ω i (by decide : (0 : Fin 3) ≤ 2)) le_rfl
  have hTH (i : ι) : T i ≤ S.χ ω := min_le_right _ _
  have hlive (i : ι) : z i ∈ survivingDomain (γ ω) (T i) := (S.actual ω i).1
  have hσeq (i : ι) (hlt : σ i < T i) : σ i = ρ (i,0) ω := by
    apply min_eq_left
    by_contra h
    have he : σ i = S.χ ω := min_eq_right (le_of_not_ge h)
    exact (not_lt_of_ge (hTH i)) (he ▸ hlt)
  have hσχ (i : ι) : σ i ≤ S.χ ω := min_le_right _ _
  have hστ (i : ι) : σ i ≤ ρ (i,2) ω :=
    (min_le_left _ _).trans (horder ω i (by decide : (0 : Fin 3) ≤ 2))
  have hstart (i : ι) (hlt : σ i < T i) :
      logFactorClock κ (logLoewnerCoordinates (G ω) (z i) (σ i)) = a i := by
    have he := (S.actual_at ω i (σ i) (hσχ i) (hστ i)).2
    have hs : actualFactorStops γ G z u₀ u₂ H (i,0) ω = σ i := (hσeq i hlt).symm
    have hc := actual_phase_switch_clock hBc hκ hw S horder ω i 0
      (by rw [hs]; exact hσχ i)
    rw [hs, he] at hc
    exact sub_eq_zero.mp (by simpa only [ite_true] using hc)
  have hend (i : ι) :
      logFactorClock κ (logLoewnerCoordinates (G ω) (z i) (T i))-a i ≤ U i := by
    have hc := cutoff_radius_strictly_reached_iff (continuous_const.mul (hBc ω))
      (hw ω) hκ (z i) (u₂ i) ((h₀ i).trans (hu i)) H (T i)
      ((hTH i).trans (S.bounded ω)) (hlive i) ω
    have hle : logFactorClock κ (logLoewnerCoordinates (G ω) (z i) (T i)) ≤
        sourceClockLevel κ (z i) (u₂ i) := by
      apply le_of_not_gt
      intro h
      have ht : ρ (i,2) ω < T i := by
        simpa only [ρ, actualFactorStops, factorRadiusLevel, Fin.reduceEq, ite_false, cutoffStop] using hc.mpr h
      exact (not_lt_of_ge (min_le_left _ _)) ht
    have he : sourceClockLevel κ (z i) (u₂ i) = a i+U i := by
      dsimp [a,U,sourceClockLevel]
      ring
    rw [he] at hle
    linarith
  have hgeo (i j : ι) (hij : i ≠ j) (hlt : σ i < T i) :
      physicalConformalRadius J (G ω) (σ i) (z i) ≤ dist (J (z i)) (J (z j)) := by
    have hc := hstart i hlt
    rw [logFactorClock_eq_logRadiusClock κ (Real.log (z i).im)] at hc
    have he : logRadiusClock (Real.log (z i).im)
        (logLoewnerCoordinates (G ω) (z i) (σ i)) = Real.log (R i/b i) := by
      dsimp [a,sourceClockLevel] at hc
      rw [← hu₀ i]
      nlinarith [hκ]
    rw [(hw ω).physical_radius_at_activation (continuous_const.mul (hBc ω)) J
      (z i) (R i) (b i) (hR i) (hb i) (hRdef i) (σ i)
      (S.actual_at ω i (σ i) (hσχ i) (hστ i)).1 he]
    exact hsep i j hij
  have hactive (t : ℝ) (ht : t ∈ Ico 0 (S.χ ω : ℝ)) (i : ι)
      (hi : i ∈ patternActiveSet (phaseAt ρ t.toNNReal ω)) :
      (σ i : ℝ) ≤ t ∧ t ≤ (T i : ℝ) := by
    have ha := (phaseAt_active_iff ρ ω i (horder ω i) t.toNNReal).mp
      (Finset.mem_filter.mp hi).2
    have htχ : t.toNNReal ≤ S.χ ω := Real.toNNReal_le_iff_le_coe.mpr ht.2.le
    constructor
    · have hh := (min_le_left (ρ (i,0) ω) (S.χ ω)).trans ha.1
      simpa only [Real.coe_toNNReal t ht.1] using (NNReal.coe_le_coe.mpr hh)
    · have hh : t.toNNReal ≤ T i := le_min ha.2.le htχ
      simpa only [Real.coe_toNNReal t ht.1] using (NNReal.coe_le_coe.mpr hh)
  have hQ (t : ℝ) (ht : t ∈ Ico 0 (S.χ ω : ℝ)) (i : ι)
      (hi : i ∈ patternActiveSet (phaseAt ρ t.toNNReal ω)) :
      S.Q t ω i = logLoewnerCoordinates (G ω) (z i) t := by
    have ha := (phaseAt_active_iff ρ ω i (horder ω i) t.toNNReal).mp
      (Finset.mem_filter.mp hi).2
    have hh := (S.actual_at ω i t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr ht.2.le) ha.2.le).2
    simpa only [Real.coe_toNNReal t ht.1] using hh
  have hrt : ∀ ω, Measurable (fun t => r t ω) :=
    fun ω => hrm.comp (measurable_id.prodMk measurable_const)
  have hri : IntervalIntegrable (fun t : ℝ => r t.toNNReal ω) volume 0 (S.χ ω : ℝ) :=
    ((bounded_rate_locallyIntegrable r hrt C hrb ω).integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hbound := actual_phase_cost_integral_le hκ hκ8 (hBc ω) (hw ω) hgrowth J hJ hJinj
    (Finset.univ : Finset ι) z (fun _ _ _ _ he => hne he) β hβ hdecay a U
    (fun i _ => mul_nonneg (div_nonneg hκ.le (by norm_num)) (sub_nonneg.mpr (hu i)))
    σ T (S.χ ω) (fun i _ => hσT i) (fun i _ => hTH i) (fun i _ => hlive i)
    (fun i _ => hstart i) (fun i _ _ => hend i)
    (fun i _ j _ hij hi _ => hgeo i j hij hi)
    (fun t => S.Q t ω) (fun t => phaseAt ρ t.toNNReal ω)
    (fun _ _ => Finset.subset_univ _) hactive hQ
    (fun t ht i hi => by
      have hh := (actual_phase_regulator hBc hκ hβ.le h₀ hu hw S horder ω t.toNNReal
        (Real.toNNReal_le_iff_le_coe.mpr ht.2.le) i (Finset.mem_filter.mp hi).2).1
      simpa only [Real.coe_toNNReal t ht.1,hQ t ht i hi] using hh)
    (fun t : ℝ => r t.toNNReal ω) hri
    (fun t ht => by
      have htχ : t.toNNReal < S.χ ω := by
        apply NNReal.coe_lt_coe.mp
        simpa only [Real.coe_toNNReal t ht.1] using ht.2
      have hh := hcost ω t.toNNReal htχ
      simpa only [Real.coe_toNNReal t ht.1] using hh)
  simpa only [discountClock,Real.toNNReal_coe] using hbound

end SLEExactGauge.Multipoint

end

end OAI
