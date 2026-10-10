import OAI.MeasureTheory.Falconer.Estimates.SmoothConvolution
import OAI.MeasureTheory.Falconer.Radial.SmoothRadialEstimate

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Metric
open scoped ENNReal NNReal

theorem sourceMollification_support_bound (α : Measure Plane) [IsFiniteMeasure α]
    {K : Set Plane} (hα : ∀ᵐ z ∂α, z ∈ K) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x : Plane) {D : ℝ} (hD : ∀ z ∈ K, dist z x ≤ D) :
    ∀ y, sourceSmoothDensity α (sourceMollifier ε hε) y ≠ 0 → dist y x ≤ D+1 := by
  intro y hy
  by_contra h
  apply hy
  apply integral_eq_zero_of_ae
  filter_upwards [hα] with z hz
  by_contra hb
  have hm : y-z ∈ ball (0 : Plane) ε := by
    rw [← sourceMollifier_support ε hε]
    exact hb
  have hd : dist y z < ε := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hm
  exact h ((dist_triangle y z x).trans ((add_le_add hd.le (hD z hz)).trans
    (by simpa only [add_comm] using add_le_add_right hε1 D)))

theorem mollified_radial_density_energy_bound (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K : Set Plane} (hK : IsCompact K)
    (hα : ∀ᵐ z ∂α, z ∈ K) {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hD : 0 < D) (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D)
    (hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((ENNReal.ofReal (sourceEnergyConstant 2 s))^(p/2) *
      (ENNReal.ofReal (sourceEnergyConstant 1 (2-s)))^(p/2)) *
      (∫⁻ x, (∫⁻ θ in Ioc 0 (2*Real.pi),
        (sourceRadialDensity (fun y => ENNReal.ofReal
          (sourceSmoothDensity α (sourceMollifier ε hε) y)) x θ)^p) ∂β) ≤
      ((ENNReal.ofReal (D+1))^p * (ENNReal.ofReal ((D+1)^(t-(2-s)*p)))^(1/2 : ℝ)) *
        ((angularEnergyConstant (t/(2-p)))^((2-p)/2) *
          (rieszEnergy β t)^(1/2 : ℝ) * (2*rieszEnergy α s)^(p/2)) := by
  let b := sourceMollifier ε hε
  have hc := sourceMollifier_compact ε hε
  have hb := sourceMollifier_smooth ε hε
  have hn := sourceMollifier_nonneg ε hε
  have h := smooth_radial_density_energy_bound (sourceSmoothDensity α b)
    (sourceSmoothDensity_compact α b hc hK hα) (sourceSmoothDensity_smooth α b hc hb)
    (sourceSmoothDensity_nonneg α b hn) β hpq hp2 hs1 hs2 (by linarith only [hD] : 0 < D+1)
    hupt htp (hdiam.mono (fun z hz => by linarith only [hz]))
    (hbound.mono (fun x hx => sourceMollification_support_bound α hα ε hε hε1 x hx))
  have he : rieszEnergy (sourceDensityMeasure (sourceSmoothDensity α b)) s ≤ rieszEnergy α s := by
    rw [← sourceSmoothDensity_measure α b hc hb.continuous hn]
    exact sourceMollifier_energy_le α ε hε (by linarith only [hs1]) hs2
  apply h.trans
  apply mul_le_mul_right
  apply mul_le_mul_right
  apply ENNReal.rpow_le_rpow _ (div_nonneg hpq.pos.le (by norm_num) : 0 ≤ p/2)
  exact mul_le_mul_right he 2

end PlanarFalconer

end OAI
