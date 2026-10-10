import OAI.MeasureTheory.Falconer.Radial.ProjectionEnergy
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem measure_power_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : Measurable F) {r q : ℝ}
    (hrq : r.HolderConjugate q) :
    (∫⁻ x, F x ∂μ)^r ≤ (μ univ)^(r-1) * (∫⁻ x, (F x)^r ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hrq hF.aemeasurable
    (g := fun _ => 1) measurable_const.aemeasurable
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_const,one_mul] at h
  have hh := ENNReal.rpow_le_rpow h hrq.nonneg
  rw [ENNReal.mul_rpow_of_nonneg _ _ hrq.nonneg,← ENNReal.rpow_mul,
    one_div_mul_cancel hrq.pos.ne',ENNReal.rpow_one,← ENNReal.rpow_mul] at hh
  have hq : (1/q)*r = r-1 := by
    rw [show (1/q)*r = r/q by ring]
    exact (div_eq_iff hrq.symm.pos.ne').mpr hrq.sub_one_mul_conj.symm
  rw [hq] at hh
  simpa only [mul_comm] using hh

theorem projection_energy_moment (μ : Measure Plane) [IsFiniteMeasure μ]
    {t r : ℝ} (ht : 0 < t) (hr : 1 < r) (htr : t*r < 1) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), (rieszEnergyOn (projectedMeasure μ θ) t)^r) ≤
      angularEnergyConstant (t*r) * (rieszEnergy μ t)^r := by
  let ρ := differenceEnergyMeasure μ t
  let : SFinite ρ := by dsimp [ρ,differenceEnergyMeasure]; infer_instance
  let F : ℝ → Plane × Plane → ℝ≥0∞ := fun θ z => sineKernel t (θ-planePhase (z.1-z.2))
  have hF : Measurable (fun z : ℝ × (Plane × Plane) => F z.1 z.2) := by
    dsimp [F,sineKernel,planePhase]
    fun_prop
  have hrq := Real.HolderConjugate.conjExponent hr
  have hmean (θ : ℝ) : (rieszEnergyOn (projectedMeasure μ θ) t)^r ≤
      (ρ univ)^(r-1) * ∫⁻ z : Plane × Plane, (F θ z)^r ∂ρ := by
    rw [projected_energy_weighted_formula μ ht]
    have hmθ : Measurable (F θ) := by dsimp [F,sineKernel,planePhase]; fun_prop
    exact measure_power_mean ρ (F θ) hmθ hrq
  have hsin (θ : ℝ) (z : Plane × Plane) :
      (F θ z)^r = sineKernel (t*r) (θ-planePhase (z.1-z.2)) := by
    dsimp [F,sineKernel]
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hint : (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), ∫⁻ z : Plane × Plane, (F θ z)^r ∂ρ) =
      angularEnergyConstant (t*r) * ρ univ := by
    rw [lintegral_lintegral_swap (hF.pow_const r).aemeasurable]
    simp_rw [hsin,sineKernel_shift_integral (mul_pos ht (zero_lt_one.trans hr)) htr]
    exact lintegral_const _
  calc
    _ ≤ ∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), (ρ univ)^(r-1) *
        (∫⁻ z : Plane × Plane, (F θ z)^r ∂ρ) := lintegral_mono hmean
    _ = (ρ univ)^(r-1) * (angularEnergyConstant (t*r) * ρ univ) := by
      rw [lintegral_const_mul _ (by fun_prop),hint]
    _ = angularEnergyConstant (t*r) * (ρ univ)^r := by
      have hp := ENNReal.rpow_add_of_nonneg (x := ρ univ) (r-1) 1 (by linarith) zero_le_one
      rw [sub_add_cancel,ENNReal.rpow_one] at hp
      rw [hp]
      ac_rfl
    _ = _ := by dsimp only [ρ]; rw [differenceEnergyMeasure_mass,rieszEnergyOn_plane]

theorem projection_energy_Lr (μ : Measure Plane) [IsFiniteMeasure μ]
    {t r : ℝ} (ht : 0 < t) (hr : 1 < r) (htr : t*r < 1) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), (rieszEnergyOn (projectedMeasure μ θ) t)^r)^(1/r) ≤
      (angularEnergyConstant (t*r))^(1/r) * rieszEnergy μ t := by
  have h := ENNReal.rpow_le_rpow (projection_energy_moment μ ht hr htr)
    (one_div_nonneg.mpr (zero_lt_one.trans hr).le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr (zero_lt_one.trans hr).le),
    ← ENNReal.rpow_mul,mul_one_div_cancel (zero_lt_one.trans hr).ne',ENNReal.rpow_one] at h
  exact h

theorem projection_energy_average (μ : Measure Plane) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), rieszEnergyOn (projectedMeasure μ θ) t) =
      angularEnergyConstant t * rieszEnergy μ t := by
  let ρ := differenceEnergyMeasure μ t
  let : SFinite ρ := by dsimp [ρ,differenceEnergyMeasure]; infer_instance
  simp_rw [projected_energy_weighted_formula μ ht]
  change (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi),
    ∫⁻ z : Plane × Plane, sineKernel t (θ-planePhase (z.1-z.2)) ∂ρ) = _
  rw [lintegral_lintegral_swap]
  · simp_rw [sineKernel_shift_integral ht ht1]
    rw [lintegral_const]
    dsimp only [ρ]
    rw [differenceEnergyMeasure_mass,rieszEnergyOn_plane]
  · have hm : Measurable (fun p : ℝ × (Plane × Plane) =>
        sineKernel t (p.1-planePhase (p.2.1-p.2.2))) := by
      unfold sineKernel planePhase
      fun_prop
    exact hm.aemeasurable

theorem projection_energy_moment_ge_one (μ : Measure Plane) [IsFiniteMeasure μ]
    {t r : ℝ} (ht : 0 < t) (hr : 1 ≤ r) (htr : t*r < 1) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), (rieszEnergyOn (projectedMeasure μ θ) t)^r) ≤
      angularEnergyConstant (t*r) * (rieszEnergy μ t)^r := by
  rcases eq_or_lt_of_le hr with he | he
  · subst r
    simpa using (projection_energy_average μ ht (by simpa using htr)).le
  · exact projection_energy_moment μ ht he htr

theorem finite_projection_moment_of_ball_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    {s C t r : ℝ} (ht : 0 < t) (hts : t < s) (hb : BallBound μ s C)
    (hr : 1 ≤ r) (htr : t*r < 1) :
    (∫⁻ θ : ℝ in Ioc 0 (2*Real.pi), (rieszEnergyOn (projectedMeasure μ θ) t)^r) < ∞ := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  exact (projection_energy_moment_ge_one μ ht hr htr).trans_lt
    (ENNReal.mul_lt_top (angularEnergyConstant_lt_top (mul_pos ht hrp) htr)
      (ENNReal.rpow_lt_top_of_nonneg hrp.le (rieszEnergy_lt_top_of_ball_bound μ ht hts hb).ne))

theorem measurable_projected_energy (μ : Measure Plane) [IsFiniteMeasure μ] (t : ℝ) :
    Measurable (fun θ => rieszEnergyOn (projectedMeasure μ θ) t) := by
  simp_rw [projected_energy_formula]
  have hm : Measurable (fun p : ℝ × (Plane × Plane) =>
      (ENNReal.ofReal |sourceProjection p.1 (p.2.1-p.2.2)|)^(-t)) := by
    unfold sourceProjection
    fun_prop
  exact hm.lintegral_prod_right

theorem projected_energy_finite_ae (μ : Measure Plane) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (he : rieszEnergy μ t < ∞) :
    ∀ᵐ θ : ℝ ∂volume.restrict (Ioc 0 (2*Real.pi)),
      rieszEnergyOn (projectedMeasure μ θ) t < ∞ := by
  apply ae_lt_top (measurable_projected_energy μ t)
  rw [projection_energy_average μ ht ht1]
  exact (ENNReal.mul_lt_top (angularEnergyConstant_lt_top ht ht1) he).ne

end PlanarFalconer

end OAI
