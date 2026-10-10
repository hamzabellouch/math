import OAI.Geometry.RCD.Heat.HeatGeneratorSecondDerivative
import OAI.Geometry.RCD.Heat.KernelHeatSpatialSource

namespace OAI

/-! # The first heat source has the actual second weak Laplacian

The source is represented by a second Sobolev function on the original
space. Both source identities use the same positive-time generator.
-/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

theorem heatAt_generator_split (f : Lp ℝ 2 μ) {a t : ℝ}
    (ha : 0 < a) (hat : a < t) :
    heatAt μ Q (t-a) (heatGeneratorAt μ Q a f) = heatGeneratorAt μ Q t f := by
  rw [heatGeneratorAt_of_pos μ Q a ha,heatGeneratorAt_of_pos μ Q t (ha.trans hat)]
  have he := heatGenerator_add μ Q (t-a) a (sub_nonneg.mpr hat.le) ha
  simpa only [sub_add_cancel,mul_apply_eq_comp] using (congrArg
    (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f) he).symm

theorem heat_generator_iterated_laplacian (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    ∃ d : SobolevSpace μ Q,
      SobolevSpace.toLp μ Q d = -heatGeneratorAt μ Q t f ∧
      IsWeakLaplacian μ Q d (heatSecondGeneratorAt μ Q t f) := by
  let a := t/2
  have ha : 0 < a := half_pos ht
  have hat : a < t := by dsimp only [a]; linarith
  have heq : t-a=a := by dsimp only [a]; ring
  let v := -heatGeneratorAt μ Q a f
  refine ⟨heatSobolev μ Q a ha v,?_,?_⟩
  · rw [heatSobolev_toLp]
    dsimp only [v]
    have hs := heatAt_generator_split μ Q f ha hat
    rw [heq] at hs
    rw [map_neg,hs]
  · have hw := heatSobolev_weak_laplacian μ Q a ha v
    simpa only [v,heatGeneratorAt_of_pos μ Q a ha,map_neg,neg_neg,
      heatSecondGeneratorAt,a] using hw

variable {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)

theorem kernelHeat_iterated_spatial_source (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    ∃ u d : SobolevSpace μ Q,
      (kernelHeat μ Q hk t f =ᵐ[μ] SobolevSpace.toLp μ Q u) ∧
      (kernelHeatGeneratorSource μ Q hk t f =ᵐ[μ] SobolevSpace.toLp μ Q d) ∧
      IsWeakLaplacian μ Q u (SobolevSpace.toLp μ Q d) ∧
      IsWeakLaplacian μ Q d (heatSecondGeneratorAt μ Q t f) := by
  obtain ⟨d,hd,hdd⟩ := heat_generator_iterated_laplacian μ Q f ht
  refine ⟨heatSobolev μ Q t ht f,d,?_,?_,?_,hdd⟩
  · simpa only [heatSobolev_toLp] using kernelHeat_represents_L2 μ Q hk ht f
  · rw [hd]
    filter_upwards [kernelHeatGeneratorSource_represents μ Q hk ht f,
      Lp.coeFn_neg (heatGeneratorAt μ Q t f)] with x hx hn
    exact hx.trans hn.symm
  · rw [hd,heatGeneratorAt_of_pos μ Q t ht]
    exact heatSobolev_weak_laplacian μ Q t ht f

end RegularPointCoordinates

end

end OAI
