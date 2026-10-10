import OAI.MeasureTheory.Falconer.Slicing.GaussianRieszScaling

namespace OAI

/-! # Finite energy survives almost every Gaussian linear projection

This is proved from Gaussian small balls and Tonelli; no projection theorem
is included among the conditional published inputs.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem gaussianRowMap_difference_continuous :
    Continuous (fun p : (Fin m → Space d) × (Space d × Space d) =>
      gaussianRowMap p.1 (p.2.1-p.2.2)) := by
  change Continuous (fun p : (Fin m → Space d) × (Space d × Space d) =>
    WithLp.toLp 2 (fun i => inner ℝ (p.1 i) (p.2.1-p.2.2)))
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi (fun i => ((continuous_apply i).comp continuous_fst).inner
    ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))

theorem gaussian_projected_energy_formula (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Fin m → Space d) (u : ℝ) :
    PlanarFalconer.rieszEnergyOn (μ.map (gaussianRowMap A)) u =
      ∫⁻ z : Space d × Space d,
        (edist (0:Space m) (gaussianRowMap A (z.1-z.2)))^(-u) ∂μ.prod μ := by
  have hm := (gaussianRowMap A).continuous.measurable
  rw [PlanarFalconer.rieszEnergyOn,Measure.map_prod_map μ μ hm hm,
    lintegral_map (by fun_prop) (hm.prodMap hm)]
  apply lintegral_congr
  intro z
  simp only [Prod.map,edist_dist,dist_eq_norm,map_sub,zero_sub,norm_neg]

theorem gaussian_projected_energy_measurable (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (u : ℝ) :
    Measurable (fun A : Fin m → Space d =>
      PlanarFalconer.rieszEnergyOn (μ.map (gaussianRowMap A)) u) := by
  simp_rw [gaussian_projected_energy_formula]
  apply Measurable.lintegral_prod_right
  exact (measurable_const.edist
    (gaussianRowMap_difference_continuous (d := d) (m := m)).measurable).pow_const _

theorem gaussian_projected_energy_average (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hum : u < (m:ℝ)) :
    (∫⁻ A : Fin m → Space d,
      PlanarFalconer.rieszEnergyOn (μ.map (gaussianRowMap A)) u ∂gaussianRows d m) ≤
      rieszSmallBallBound m (gaussianBandConstant^m) u * PlanarFalconer.rieszEnergyOn μ u := by
  let F : (Fin m → Space d) → (Space d × Space d) → ℝ≥0∞ :=
    fun A z => (edist (0:Space m) (gaussianRowMap A (z.1-z.2)))^(-u)
  have hF : Measurable (Function.uncurry F) := by
    exact (measurable_const.edist
      (gaussianRowMap_difference_continuous (d := d) (m := m)).measurable).pow_const _
  simp_rw [gaussian_projected_energy_formula]
  change (∫⁻ A, ∫⁻ z, F A z ∂μ.prod μ ∂gaussianRows d m) ≤ _
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc
    _ ≤ ∫⁻ z : Space d × Space d,
        rieszSmallBallBound m (gaussianBandConstant^m) u * (edist z.1 z.2)^(-u) ∂μ.prod μ := by
      apply lintegral_mono
      intro z
      simpa only [F,edist_dist,dist_eq_norm,zero_sub,norm_neg] using
        gaussianRows_inverse_moment hu hum (z.1-z.2)
    _ = _ := lintegral_const_mul' _ _ (rieszSmallBallBound_lt_top hum).ne

theorem gaussian_projected_energy_finite_ae (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 < u) (hum : u < (m:ℝ))
    (henergy : PlanarFalconer.rieszEnergyOn μ u < ∞) :
    ∀ᵐ A : Fin m → Space d ∂gaussianRows d m,
      PlanarFalconer.rieszEnergyOn (μ.map (gaussianRowMap A)) u < ∞ := by
  apply ae_lt_top (gaussian_projected_energy_measurable μ u)
  exact ((gaussian_projected_energy_average μ hu hum).trans_lt
    (ENNReal.mul_lt_top (rieszSmallBallBound_lt_top hum) henergy)).ne

end Falconer

end OAI
