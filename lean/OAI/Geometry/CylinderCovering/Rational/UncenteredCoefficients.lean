import OAI.Geometry.CylinderCovering.Rational.UncenteredCoefficientsDefinitions
import OAI.Geometry.CylinderCovering.Rational.CostDictionary
import OAI.Geometry.CylinderCovering.Rational.EnergyIntegral
import OAI.Geometry.CylinderCovering.Rational.CeilingIntegral

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RationalDictionary

theorem uncenteredBaseDomain_measurable : MeasurableSet uncenteredBaseDomain := by
  unfold uncenteredBaseDomain
  measurability

theorem labelMap_baseDomain_iff (p : Plane) :
    p ∈ uncenteredBaseDomain ↔ labelMap p ∈ SlopeRational.baseDomain := by
  change (0 ≤ p 1 ∧ p 1 ≤ 1 ∧ |p 0| ≤ c0 * p 1) ↔
    (2 * |ell * p 0| ≤ 1 / 2 - (1 - p 1) / 2 ∧ 0 ≤ (1 - p 1) / 2)
  constructor
  · rintro ⟨hp₀, hp₁, hpw⟩
    exact ⟨(wedge_iff _ _).mp hpw, by linarith⟩
  · rintro ⟨hpw, hp₁⟩
    have hw := (wedge_iff (p 0) (p 1)).mpr hpw
    exact ⟨by nlinarith [abs_nonneg (p 0), c0_pos], by linarith, hw⟩

theorem labelMap_image_baseDomain :
    labelMap '' uncenteredBaseDomain = SlopeRational.baseDomain := by
  apply Set.Subset.antisymm
  · rintro z ⟨p, hp, rfl⟩
    exact (labelMap_baseDomain_iff p).mp hp
  · intro z hz
    refine ⟨inverseLabelMap z, ?_, labelMap_inverseLabelMap z⟩
    apply (labelMap_baseDomain_iff _).mpr
    simpa only [labelMap_inverseLabelMap] using hz

theorem integral_base_change (f : Plane → ℝ) :
    (∫ z in SlopeRational.baseDomain, f z) =
      (ell / 2) * ∫ p in uncenteredBaseDomain, f (labelMap p) := by
  rw [← labelMap_image_baseDomain]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    uncenteredBaseDomain_measurable
    (fun p _ => (labelMap_hasFDerivAt p).hasFDerivWithinAt)
    labelMap_injective.injOn]
  rw [labelDerivative_det]
  have ha : |-ell / 2| = ell / 2 := by
    rw [neg_div, abs_neg, abs_of_pos (div_pos ell_pos (by norm_num))]
  rw [ha]
  simp only [smul_eq_mul]
  exact integral_const_mul _ _

theorem velocity_norm_sq_dictionary {d0 : ℝ} (hd : 0 < d0) {p : Plane}
    (hp : p ∈ uncenteredBaseDomain) :
    ‖velocity d0 p‖ ^ 2 = (4 * (1 + d0)) ^ 2 *
      SlopeRational.energyDensity (d0 / 2) (labelMap p) := by
  have hs : p 1 + d0 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hp.1 hd)
  have h := squared_slope_dictionary hs 1 (p 0)
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [velocity, vec2, Fin.sum_univ_two]
  simpa [centeredTilt, SlopeRational.energyDensity, labelMap, vec2, c0_sq] using h.symm

theorem uncenteredEnergyIntegral_dictionary {d0 : ℝ} (hd : 0 < d0) :
    uncenteredEnergyIntegral d0 =
      coefficientScale d0 * SlopeRational.energyIntegral (d0 / 2) := by
  have hi : (∫ p in uncenteredBaseDomain, ‖velocity d0 p‖ ^ 2) =
      (4 * (1 + d0)) ^ 2 *
        ∫ p in uncenteredBaseDomain, SlopeRational.energyDensity (d0 / 2) (labelMap p) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun uncenteredBaseDomain_measurable
    intro p hp
    exact velocity_norm_sq_dictionary hd hp
  unfold uncenteredEnergyIntegral SlopeRational.energyIntegral coefficientScale
  rw [hi, integral_base_change]
  field_simp [ell_ne_zero]
  ring

theorem uncenteredCeilingIntegral_dictionary {d0 : ℝ} (hd : 0 < d0) :
    uncenteredCeilingIntegral d0 =
      coefficientScale d0 * SlopeRational.ceilingIntegral (d0 / 2) := by
  have hd' : 1 + d0 ≠ 0 := by linarith
  have hp (u : ℝ) : a0 d0 u = 32 * (1 + d0) ^ 2 *
      SlopeRational.ceilingPolynomial (d0 / 2) (ell * u) := by
    rw [ceiling_dictionary hd']
    field_simp
  unfold uncenteredCeilingIntegral coefficientScale SlopeRational.ceilingIntegral
  simp_rw [hp]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ ell_ne_zero]
  have hn : ell * -c0 = -(1 / 4 : ℝ) := by rw [mul_neg, ell_mul_c0]
  rw [hn, ell_mul_c0]
  simp only [smul_eq_mul]
  ring_nf

end RationalDictionary

end

end OAI
