import OAI.Geometry.RCD.Heat.HeatGeneratorTimeContinuity

namespace OAI

/-! # Joint continuity of the backward heat values and sources -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)

theorem kernelHeat_backward_continuousOn (g : Lp ℝ 2 μ) (T : ℝ) :
    ContinuousOn (fun sx : ℝ × X => kernelHeat μ Q hk (T-sx.1) g sx.2)
      (Iio T ×ˢ univ) := by
  let τ := fun sx : ℝ × X => (T-sx.1,sx.2)
  have hτ : Continuous τ := (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hm : MapsTo τ (Iio T ×ˢ univ) (Ioi (0:ℝ) ×ˢ (univ : Set X)) := by
    intro sx hsx
    constructor
    · change 0 < T-sx.1
      exact sub_pos.mpr hsx.1
    · exact mem_univ _
  exact ContinuousOn.comp (f := τ) (kernelHeat_continuousOn_time_space μ Q hk g)
    hτ.continuousOn hm

theorem kernelHeatGeneratorSource_backward_continuousOn (g : Lp ℝ 2 μ) (T : ℝ) :
    ContinuousOn (fun sx : ℝ × X => kernelHeatGeneratorSource μ Q hk (T-sx.1) g sx.2)
      (Iio T ×ˢ univ) := by
  let τ := fun sx : ℝ × X => (T-sx.1,sx.2)
  have hτ : Continuous τ := (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hm : MapsTo τ (Iio T ×ˢ univ) (Ioi (0:ℝ) ×ˢ (univ : Set X)) := by
    intro sx hsx
    constructor
    · change 0 < T-sx.1
      exact sub_pos.mpr hsx.1
    · exact mem_univ _
  exact ContinuousOn.comp (f := τ) (kernelHeatGeneratorSource_continuousOn_time_space μ Q hk g)
    hτ.continuousOn hm

end RegularPointCoordinates

end

end OAI
