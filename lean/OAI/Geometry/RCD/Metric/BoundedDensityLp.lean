import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Actual L² densities for bounded probability measures with bounded support -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [SigmaFinite μ] (hQ : QuadraticCheegerEnergy μ)

theorem exists_bounded_probability_density (ν : Measure X) [IsProbabilityMeasure ν]
    {C : ℝ≥0} (hC : ν ≤ ENNReal.ofReal C • μ) (p : X) {R : ℝ}
    (hs : ∀ᵐ x ∂ν, dist x p ≤ R) :
    ∃ f : Lp ℝ 2 μ, 0 ≤ f ∧ (∀ᵐ x ∂μ, f x ≤ C) ∧ (∫ x, f x ∂μ)=1 ∧
      (∀ᵐ x ∂μ, f x≠0 → dist p x ≤ R) ∧ heatMeasure μ hQ 0 f=ν := by
  let B := closedBall p R
  let ρ := B.indicator (fun x => min (C:ℝ) (ν.rnDeriv μ x).toReal)
  have hρ : Measurable ρ :=
    (measurable_const.min (ν.measurable_rnDeriv μ).ennreal_toReal).indicator measurableSet_closedBall
  have hρ0 (x : X) : 0 ≤ ρ x :=
    indicator_nonneg (fun _ _ => le_min C.coe_nonneg ENNReal.toReal_nonneg) x
  have hρC (x : X) : ρ x ≤ C := by
    by_cases hx : x ∈ B
    · exact (indicator_of_mem hx _).trans_le (min_le_left _ _)
    · simpa only [ρ,indicator_of_notMem hx] using C.coe_nonneg
  have hρS (x : X) (hx : R < dist p x) : ρ x=0 := by
    apply indicator_of_notMem
    simpa only [B,mem_closedBall,not_le,dist_comm] using hx
  have hρmem : MemLp ρ 2 μ := memLp_of_bounded_ball_support μ hρ p R C hρS
    (fun x => by rw [abs_of_nonneg (hρ0 x)]; exact hρC x)
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hC
  have he : ρ =ᵐ[μ] fun x => (ν.rnDeriv μ x).toReal := by
    filter_upwards [rnDeriv_le_const_of_le_smul μ ν hC,Measure.rnDeriv_lt_top ν μ,
      rnDeriv_eq_indicator_of_supported μ ν measurableSet_closedBall hs] with x hc hct hsup
    by_cases hx : x ∈ B
    · rw [show ρ x=min (C:ℝ) (ν.rnDeriv μ x).toReal from indicator_of_mem hx _]
      apply min_eq_right
      exact (ENNReal.toReal_le_toReal hct.ne ENNReal.ofReal_ne_top).mpr hc |>.trans_eq
        (ENNReal.toReal_ofReal C.coe_nonneg)
    · have hz : ν.rnDeriv μ x=0 := by simpa only [B,indicator_of_notMem hx] using hsup
      simp only [ρ,indicator_of_notMem hx,hz,ENNReal.toReal_zero]
  let f := hρmem.toLp ρ
  have hf : f =ᵐ[μ] ρ := hρmem.coeFn_toLp
  refine ⟨f,(Lp.coeFn_nonneg _).mp (hf.mono fun x hx => hx ▸ hρ0 x),
    hf.mono (fun x hx => hx ▸ hρC x),?_,?_,?_⟩
  · rw [integral_congr_ae (hf.trans he),Measure.integral_toReal_rnDeriv hac]
    simp only [Measure.real,measure_univ,ENNReal.toReal_one]
  · filter_upwards [hf] with x hx hne
    by_contra h
    exact hne (hx.trans (hρS x (lt_of_not_ge h)))
  · simp only [heatMeasure,heatAt_zero,one_apply_eq_self]
    have hfr : (fun x => ENNReal.ofReal (f x)) =ᵐ[μ]
        fun x => ENNReal.ofReal (ν.rnDeriv μ x).toReal :=
      (hf.trans he).mono fun _ hx => congrArg ENNReal.ofReal hx
    rw [withDensity_congr_ae hfr]
    exact withDensity_ofReal_rnDeriv μ ν hac

end RegularPointCoordinates

end

end OAI
