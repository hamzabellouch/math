import OAI.MathematicalPhysics.Boltzmann.Branching.HotGainReduction

namespace OAI

/-!
# The positive disk mixture for the truncated transverse power

The hot-gain estimate uses the finite measure with density
`(1 + ‖p‖⁻ᑫ) 1_{‖p‖ < D}`. Its singular part is a positive radius mixture
of centered disks. Values at the origin are irrelevant for this identity.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture

namespace BoltzmannNonuniqueness.PowerDiskMixture

def mixingDensity (q a : ℝ) : ℝ := Real.pi * q * a ^ (1 - q)

def cutoffDensity (q D : ℝ) (p : Transverse) : ℝ :=
  (ball (0 : Transverse) D).indicator (fun p => 1 + ‖p‖ ^ (-q)) p

theorem integral_power_tail {q r D : ℝ} (hq : 0 < q) (hr : 0 < r) (hrD : r ≤ D) :
    (∫ a in Ioc r D, q * a ^ (-q - 1)) = r ^ (-q) - D ^ (-q) := by
  have hz : (0 : ℝ) ∉ uIcc r D := by
    rw [uIcc_of_le hrD]
    simp only [mem_Icc, not_and_or, not_le]
    exact Or.inl hr
  rw [← intervalIntegral.integral_of_le hrD, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by linarith, hz⟩)]
  rw [show -q - 1 + 1 = -q by ring]
  field_simp
  ring

theorem mixingDensity_nonneg {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) :
    0 ≤ mixingDensity q a := by
  unfold mixingDensity
  exact mul_nonneg (mul_nonneg Real.pi_pos.le hq) (Real.rpow_nonneg ha _)

theorem measurable_mixingDensity (q : ℝ) : Measurable (mixingDensity q) := by
  unfold mixingDensity
  fun_prop

theorem integrableOn_mixingDensity {q D : ℝ} (hq : q < 2) (hD : 0 ≤ D) :
    IntegrableOn (mixingDensity q) (Ioc 0 D) := by
  have hi : IntervalIntegrable (fun a : ℝ => a ^ (1 - q)) volume 0 D :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hD).mp hi).const_mul (Real.pi * q)

theorem integral_mixingDensity {q D : ℝ} (hq : q < 2) (hD : 0 ≤ D) :
    (∫ a in Ioc 0 D, mixingDensity q a) =
      Real.pi * q / (2 - q) * D ^ (2 - q) := by
  unfold mixingDensity
  rw [← intervalIntegral.integral_of_le hD, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < 1 - q))]
  rw [show 1 - q + 1 = 2 - q by ring, Real.zero_rpow (by linarith : 2 - q ≠ 0)]
  ring

theorem layerCake_integrand (q : ℝ) (p : Transverse) {a : ℝ} (ha : 0 < a) :
    mixingDensity q a * diskDensity a p =
      (Ioi ‖p‖).indicator (fun a => q * a ^ (-q - 1)) a := by
  have hp : a ^ (1 - q) = a ^ (-q - 1) * a ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha]
    congr 1
    ring
  by_cases hm : ‖p‖ < a
  · rw [diskDensity_eq_ite, ite_eq_left hm, indicator_of_mem (show a ∈ Ioi ‖p‖ from hm)]
    unfold mixingDensity
    rw [hp]
    field_simp
  · rw [diskDensity_eq_ite, ite_eq_right hm, mul_zero,
      indicator_of_notMem (show a ∉ Ioi ‖p‖ from hm)]

/-- The singular radial density is a positive mixture of disks, away from its null origin. -/
theorem density_layerCake {q D : ℝ} (hq : 0 < q) (_hD : 0 < D)
    {p : Transverse} (hp : p ≠ 0) :
    cutoffDensity q D p =
      (1 + D ^ (-q)) * (ball (0 : Transverse) D).indicator (fun _ => 1) p +
        ∫ a in Ioc 0 D, mixingDensity q a * diskDensity a p := by
  have hr : 0 < ‖p‖ := norm_pos_iff.mpr hp
  by_cases hpd : ‖p‖ < D
  · have hi : Ioi ‖p‖ ∩ Ioc (0 : ℝ) D = Ioc ‖p‖ D := by
      ext a
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · tauto
      · intro ha
        exact ⟨ha.1, lt_trans hr ha.1, ha.2⟩
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun a ha => layerCake_integrand q p ha.1),
      integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      hi, integral_power_tail hq hr hpd.le]
    simp only [cutoffDensity, indicator_of_mem (mem_ball_zero_iff.mpr hpd), mul_one]
    ring
  · have he : (∫ a in Ioc (0 : ℝ) D, mixingDensity q a * diskDensity a p) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      have hpa : ¬‖p‖ < a := not_lt.mpr (ha.2.trans (le_of_not_gt hpd))
      rw [diskDensity_eq_ite, ite_eq_right hpa, mul_zero]
      rfl
    rw [he]
    simp only [cutoffDensity, indicator_of_notMem (show p ∉ ball (0 : Transverse) D from
      fun h => hpd (mem_ball_zero_iff.mp h)), mul_zero, add_zero]

theorem layerCake_indicator (q D : ℝ) (p : Transverse) :
    (Ioc (0 : ℝ) D).indicator (fun a => mixingDensity q a * diskDensity a p) =
      (Ioc ‖p‖ D).indicator (fun a => q * a ^ (-q - 1)) := by
  funext a
  by_cases ha : a ∈ Ioc (0 : ℝ) D
  · rw [indicator_of_mem ha, layerCake_integrand q p ha.1]
    by_cases hp : ‖p‖ < a
    · rw [indicator_of_mem (show a ∈ Ioi ‖p‖ from hp),
        indicator_of_mem (show a ∈ Ioc ‖p‖ D from ⟨hp, ha.2⟩)]
    · rw [indicator_of_notMem (show a ∉ Ioi ‖p‖ from hp),
        indicator_of_notMem (show a ∉ Ioc ‖p‖ D from fun h => hp h.1)]
  · rw [indicator_of_notMem ha,
      indicator_of_notMem (show a ∉ Ioc ‖p‖ D from fun h =>
        ha ⟨lt_of_le_of_lt (norm_nonneg p) h.1, h.2⟩)]

theorem integrableOn_layerCake (q D : ℝ) {p : Transverse} (hp : p ≠ 0) :
    IntegrableOn (fun a => mixingDensity q a * diskDensity a p) (Ioc 0 D) := by
  rw [← integrable_indicator_iff measurableSet_Ioc, layerCake_indicator,
    integrable_indicator_iff measurableSet_Ioc]
  have hc : ContinuousOn (fun a : ℝ => q * a ^ (-q - 1)) (Icc ‖p‖ D) := by
    apply continuousOn_const.mul
    apply continuousOn_id.rpow_const
    intro a ha
    exact Or.inl (ne_of_gt (lt_of_lt_of_le (norm_pos_iff.mpr hp) ha.1))
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

def boundaryMass (q D : ℝ) : ℝ := (1 + D ^ (-q)) * (Real.pi * D ^ 2)

theorem boundaryMass_nonneg (q : ℝ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ boundaryMass q D := by
  unfold boundaryMass
  exact mul_nonneg (add_nonneg zero_le_one (Real.rpow_nonneg hD _))
    (mul_nonneg Real.pi_pos.le (sq_nonneg D))

theorem lintegral_density_layerCake {q D : ℝ} (hq : 0 < q) (hD : 0 < D)
    {p : Transverse} (hp : p ≠ 0) :
    ENNReal.ofReal (cutoffDensity q D p) =
      ENNReal.ofReal (boundaryMass q D) * ENNReal.ofReal (diskDensity D p) +
        ∫⁻ a in Ioc 0 D, ENNReal.ofReal (mixingDensity q a * diskDensity a p) := by
  have hn : ∀ᵐ a ∂volume.restrict (Ioc (0 : ℝ) D),
      0 ≤ mixingDensity q a * diskDensity a p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact mul_nonneg (mixingDensity_nonneg hq.le ha.1.le) (diskDensity_nonneg a p)
  have hi := ofReal_integral_eq_lintegral_ofReal (integrableOn_layerCake q D hp) hn
  have hb : 0 ≤ (1 + D ^ (-q)) * (ball (0 : Transverse) D).indicator (fun _ => (1 : ℝ)) p :=
    mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => by norm_num) p)
  rw [density_layerCake hq hD hp, ENNReal.ofReal_add hb
    (integral_nonneg_of_ae hn), hi]
  congr 1
  rw [← ENNReal.ofReal_mul (boundaryMass_nonneg q hD.le)]
  apply congrArg ENNReal.ofReal
  by_cases hm : p ∈ ball (0 : Transverse) D
  · rw [indicator_of_mem hm, diskDensity, indicator_of_mem hm]
    unfold boundaryMass
    field_simp
  · rw [indicator_of_notMem hm, diskDensity, indicator_of_notMem hm, mul_zero, mul_zero]

theorem measurable_diskDensity_fixed (a : ℝ) : Measurable (diskDensity a) := by
  have hm : Measurable (fun p : Transverse => (a, p)) := measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using measurable_diskDensity.comp hm

/-- Tonelli's theorem turns the density identity into a positive mixture for
every nonnegative measurable test, including singular kernel tests. -/
theorem lintegral_cutoff_mixture {q D : ℝ} (hq : 0 < q) (hD : 0 < D)
    (φ : Transverse → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, ENNReal.ofReal (cutoffDensity q D p) * φ p) =
      ENNReal.ofReal (boundaryMass q D) *
        (∫⁻ p, ENNReal.ofReal (diskDensity D p) * φ p) +
      ∫⁻ a in Ioc 0 D, ENNReal.ofReal (mixingDensity q a) *
        (∫⁻ p, ENNReal.ofReal (diskDensity a p) * φ p) := by
  have hprod : Measurable (fun pa : Transverse × ℝ =>
      ENNReal.ofReal (mixingDensity q pa.2 * diskDensity pa.2 pa.1) * φ pa.1) := by
    exact (((measurable_mixingDensity q).comp measurable_snd).mul
      (measurable_diskDensity.comp measurable_swap)).ennreal_ofReal.mul
        (hφ.comp measurable_fst)
  have hbase : Measurable (fun p : Transverse =>
      ENNReal.ofReal (boundaryMass q D) * ENNReal.ofReal (diskDensity D p) * φ p) :=
    (measurable_const.mul (measurable_diskDensity_fixed D).ennreal_ofReal).mul hφ
  calc
    _ = ∫⁻ p, ENNReal.ofReal (boundaryMass q D) * ENNReal.ofReal (diskDensity D p) * φ p +
        ∫⁻ a in Ioc 0 D, ENNReal.ofReal (mixingDensity q a * diskDensity a p) * φ p := by
      apply lintegral_congr_ae
      filter_upwards [volume.ae_ne (0 : Transverse)] with p hp
      rw [lintegral_density_layerCake hq hD hp, add_mul]
      have hm : Measurable (fun a : ℝ => ENNReal.ofReal (mixingDensity q a * diskDensity a p)) :=
        ((measurable_mixingDensity q).mul
          (measurable_diskDensity.comp (measurable_id.prodMk measurable_const))).ennreal_ofReal
      rw [lintegral_mul_const (φ p) hm]
    _ = ENNReal.ofReal (boundaryMass q D) *
        (∫⁻ p, ENNReal.ofReal (diskDensity D p) * φ p) +
        ∫⁻ a in Ioc 0 D, ∫⁻ p,
          ENNReal.ofReal (mixingDensity q a * diskDensity a p) * φ p := by
      rw [lintegral_add_left hbase]
      have hb : Measurable (fun p => ENNReal.ofReal (diskDensity D p) * φ p) :=
        (measurable_diskDensity_fixed D).ennreal_ofReal.mul hφ
      rw [show (fun p => ENNReal.ofReal (boundaryMass q D) *
          ENNReal.ofReal (diskDensity D p) * φ p) =
        (fun p => ENNReal.ofReal (boundaryMass q D) *
          (ENNReal.ofReal (diskDensity D p) * φ p)) by funext p; rw [mul_assoc],
        lintegral_const_mul _ hb, lintegral_lintegral_swap hprod.aemeasurable]
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      simp_rw [ENNReal.ofReal_mul (mixingDensity_nonneg hq.le ha.1.le), mul_assoc]
      exact lintegral_const_mul _ ((measurable_diskDensity_fixed a).ennreal_ofReal.mul hφ)

end BoltzmannNonuniqueness.PowerDiskMixture

end

end OAI
