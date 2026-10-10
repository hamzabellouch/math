import OAI.MeasureTheory.Falconer.Geometry.ProjectionKernel
import OAI.MeasureTheory.Falconer.Radial.ProjectionMoment

namespace OAI

/-! Riesz-energy moments for actual orthogonal hyperplane projections. -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def hyperplaneProjectedMeasure {d : ℕ} (μ : Measure (Space d))
    (w : Sphere d) : Measure (Space d) :=
  μ.map (perpendicularPart (w : Space d))

theorem hyperplane_projected_energy_formula {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (s : ℝ) (w : Sphere d) :
    PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s =
      ∫⁻ z : Space d × Space d,
        (ENNReal.ofReal ‖perpendicularPart (w : Space d) (z.1-z.2)‖)^(-s) ∂μ.prod μ := by
  have hm : Measurable (perpendicularPart (w : Space d)) := by
    unfold perpendicularPart
    fun_prop
  rw [PlanarFalconer.rieszEnergyOn, hyperplaneProjectedMeasure,
    Measure.map_prod_map μ μ hm hm, lintegral_map (by fun_prop) (hm.prodMap hm)]
  apply lintegral_congr
  intro z
  simp only [Prod.map, edist_dist, dist_eq_norm, perpendicularPart_sub]

noncomputable def euclideanDifferenceEnergyMeasure {d : ℕ} (μ : Measure (Space d))
    (s : ℝ) : Measure (Space d × Space d) :=
  (μ.prod μ).withDensity (fun z => (edist z.1 z.2)^(-s))

theorem euclideanDifferenceEnergyMeasure_mass {d : ℕ} (μ : Measure (Space d)) (s : ℝ) :
    euclideanDifferenceEnergyMeasure μ s univ = PlanarFalconer.rieszEnergyOn μ s := by
  rw [euclideanDifferenceEnergyMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  rfl

theorem hyperplane_projected_energy_weighted {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (s : ℝ) (w : Sphere d) :
    PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s =
      ∫⁻ z : Space d × Space d, directionalProjectionKernel s w (z.1-z.2)
        ∂euclideanDifferenceEnergyMeasure μ s := by
  have hm : Measurable (fun z : Space d × Space d =>
      directionalProjectionKernel s w (z.1-z.2)) :=
    (directionalProjectionKernel_measurable s).comp
      (measurable_const.prodMk (measurable_fst.sub measurable_snd))
  rw [hyperplane_projected_energy_formula, euclideanDifferenceEnergyMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hm]
  apply lintegral_congr
  intro z
  simp only [Pi.mul_apply, edist_dist, dist_eq_norm]
  exact projection_kernel_factor s w (z.1-z.2)

theorem hyperplane_projected_energy_measurable {d : ℕ} (μ : Measure (Space d))
    [IsFiniteMeasure μ] (s : ℝ) :
    Measurable (fun w : Sphere d =>
      PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s) := by
  simp_rw [hyperplane_projected_energy_formula]
  apply Measurable.lintegral_prod_right
  unfold perpendicularPart
  fun_prop

theorem hyperplane_projected_energy_moment (n : ℕ) {s r : ℝ}
    (hs : 0 < s) (hr : 1 < r) (hsr : s*r < n) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (μ : Measure (Space (n+1))) [IsFiniteMeasure μ],
      (∫⁻ w : Sphere (n+1),
        (PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s)^r
          ∂sphereMeasure (n+1)) ≤ C * (PlanarFalconer.rieszEnergyOn μ s)^r := by
  obtain ⟨C,hC,hangular⟩ := directionalProjectionKernel_angular_bound n
    (mul_pos hs (zero_lt_one.trans hr)) hsr
  refine ⟨C,hC,?_⟩
  intro μ hμ
  let ρ := euclideanDifferenceEnergyMeasure μ s
  let : SFinite ρ := by dsimp [ρ, euclideanDifferenceEnergyMeasure]; infer_instance
  let F := fun (w : Sphere (n+1)) (z : Space (n+1) × Space (n+1)) =>
    directionalProjectionKernel s w (z.1-z.2)
  have hF : Measurable (Function.uncurry F) := by
    exact (directionalProjectionKernel_measurable s).comp
      (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).sub
        (measurable_snd.comp measurable_snd)))
  have hmean (w : Sphere (n+1)) :
      (PlanarFalconer.rieszEnergyOn (hyperplaneProjectedMeasure μ w) s)^r ≤
        (ρ univ)^(r-1) * ∫⁻ z, (F w z)^r ∂ρ := by
    rw [hyperplane_projected_energy_weighted μ s]
    exact PlanarFalconer.measure_power_mean ρ (F w)
      (hF.comp (measurable_const.prodMk measurable_id)) (Real.HolderConjugate.conjExponent hr)
  have hint : (∫⁻ w : Sphere (n+1), ∫⁻ z, (F w z)^r ∂ρ ∂sphereMeasure (n+1)) ≤
      C * ρ univ := by
    rw [lintegral_lintegral_swap (hF.pow_const r).aemeasurable]
    calc
      _ ≤ ∫⁻ _z, C ∂ρ := by
        apply lintegral_mono
        intro z
        simp only [F, directionalProjectionKernel_rpow]
        exact hangular (z.1-z.2)
      _ = _ := lintegral_const C
  calc
    _ ≤ ∫⁻ w : Sphere (n+1), (ρ univ)^(r-1) * (∫⁻ z, (F w z)^r ∂ρ)
        ∂sphereMeasure (n+1) := lintegral_mono hmean
    _ = (ρ univ)^(r-1) * (∫⁻ w : Sphere (n+1), ∫⁻ z, (F w z)^r ∂ρ
        ∂sphereMeasure (n+1)) := lintegral_const_mul _ (by fun_prop)
    _ ≤ (ρ univ)^(r-1) * (C * ρ univ) := mul_le_mul_right hint _
    _ = C * (PlanarFalconer.rieszEnergyOn μ s)^r := by
      have hp := ENNReal.rpow_add_of_nonneg (x := ρ univ) (r-1) 1 (by linarith) zero_le_one
      rw [sub_add_cancel, ENNReal.rpow_one] at hp
      calc
        _ = C * ((ρ univ)^(r-1) * ρ univ) := by ac_rfl
        _ = C * (ρ univ)^r := by rw [← hp]
        _ = _ := by rw [show ρ univ = PlanarFalconer.rieszEnergyOn μ s from
          euclideanDifferenceEnergyMeasure_mass μ s]

end Falconer

end OAI
