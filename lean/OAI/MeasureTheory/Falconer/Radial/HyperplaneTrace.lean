import OAI.MeasureTheory.Falconer.Radial.HyperplaneFourier
import OAI.MeasureTheory.Falconer.Graphs.SmoothFiberEstimate

namespace OAI

/-! The hyperplane trace bound with its actual source and pin energies. -/

namespace Falconer
open Set MeasureTheory PlanarFalconer
open scoped ENNReal SchwartzMap FourierTransform

theorem hyperplaneProjection_dist_le {n : ℕ} (w : Sphere (n+1)) (x y : Space (n+1)) :
    dist (hyperplaneProjection w x) (hyperplaneProjection w y) ≤ dist x y := by
  rw [hyperplaneProjection_dist, dist_eq_norm, ← perpendicularPart_sub, dist_eq_norm]
  exact norm_perpendicularPart_le (sphere_norm w) _

theorem hyperplaneCoordinateMeasure_diameter {n : ℕ} (β : Measure (Space (n+1)))
    [IsFiniteMeasure β] {D : ℝ}
    (hD : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D)
    (w : Sphere (n+1)) :
    ∀ᵐ z : Space n × Space n ∂(hyperplaneCoordinateMeasure β w).prod
      (hyperplaneCoordinateMeasure β w), dist z.1 z.2 ≤ D := by
  have hm := (contDiff_hyperplaneProjection w).continuous.measurable
  rw [hyperplaneCoordinateMeasure, Measure.map_prod_map β β hm hm,
    ae_map_iff (hm.prodMap hm).aemeasurable (by measurability)]
  filter_upwards [hD] with z hz
  exact (hyperplaneProjection_dist_le w z.1 z.2).trans hz

theorem hyperplane_smooth_fiber_bound {n : ℕ} (a : Space (n+1) → ℝ)
    (hc : HasCompactSupport a) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hn : ∀ x, 0 ≤ a x)
    (β : Measure (Space (n+1))) [IsFiniteMeasure β] {D s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hs : (n : ℝ) < s) (hs2 : s < 2*n)
    (hD : 0 < D) (hupt : (2*n-s)*p < t)
    (hdiam : ∀ᵐ z : Space (n+1) × Space (n+1) ∂β.prod β, dist z.1 z.2 ≤ D)
    (w : Sphere (n+1)) :
    (ENNReal.ofReal (sourceEnergyConstant n (2*n-s)))^(p/2) *
      (∫⁻ y : Space n, (hyperplaneFiberDensity (fun x => ENNReal.ofReal (a x)) w y)^p
        ∂hyperplaneCoordinateMeasure β w) ≤
      (ENNReal.ofReal (D^(t-(2*n-s)*p)))^(1/2 : ℝ) *
        (rieszEnergyOn (hyperplaneProjectedMeasure β w) t)^(1/2 : ℝ) *
        (hyperplaneFourierEnergy (euclideanDensityMeasure a) s w)^(p/2) := by
  let : IsFiniteMeasure (hyperplaneCoordinateMeasure β w) := by
    unfold hyperplaneCoordinateMeasure
    infer_instance
  have h := euclidean_lp_trace (hyperplaneCoordinateMeasure β w)
    (hyperplaneSchwartzFiber a hc ha w) (hyperplaneSchwartzFiber_nonneg a hc ha hn w)
    hpq (by linarith) (by linarith) hD hupt (hyperplaneCoordinateMeasure_diameter β hdiam w)
  rw [show (n : ℝ)-(2*n-s) = s-n by ring,
    hyperplaneSchwartzFiber_energy a hc ha hn w s,
    hyperplaneCoordinateMeasure_energy] at h
  have hr := ENNReal.rpow_le_rpow h hpq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ENNReal.mul_rpow_of_nonneg _ _ hpq.nonneg,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    show (1/2 : ℝ)*p = p/2 by ring,
    show (1/(2*p))*p = (1/2 : ℝ) by field_simp [hpq.pos.ne'],
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2),
    eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hpq.pos).ne' ENNReal.ofReal_ne_top
      (hyperplaneSchwartzFiber a hc ha w).continuous.aestronglyMeasurable,
    ENNReal.toReal_ofReal hpq.nonneg,
    eLpNorm_nonneg_rpow _ _ (hyperplaneSchwartzFiber_nonneg a hc ha hn w) hpq.pos] at hr
  simpa only [hyperplaneSchwartzFiber_density a hc ha hn w, mul_assoc] using hr

end Falconer

end OAI
