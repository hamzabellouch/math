import OAI.Geometry.CylinderCovering.Rational.DictionaryCoefficientsDefinitions
import OAI.Geometry.CylinderCovering.Rational.DictionaryCost
import OAI.Geometry.CylinderCovering.Rational.EnergyIntegral
import OAI.Geometry.CylinderCovering.Rational.CeilingIntegral

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RationalDictionary

lemma coefficientBaseDomain_measurable : MeasurableSet coefficientBaseDomain := by
  have h1 : MeasurableSet {p : Plane | 0 ≤ p 1} :=
    measurableSet_le measurable_const (by fun_prop)
  have h2 : MeasurableSet {p : Plane | p 1 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have h3 : MeasurableSet {p : Plane | |p 0| ≤ c0 * p 1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter h3)

lemma labelMap_coefficientBaseDomain_iff (p : Plane) :
    p ∈ coefficientBaseDomain ↔ labelMap p ∈ SlopeRational.baseDomain := by
  change (0 ≤ p 1 ∧ p 1 ≤ 1 ∧ |p 0| ≤ c0 * p 1) ↔
    (2 * |ell * p 0| ≤ 1 / 2 - (1 - p 1) / 2 ∧ 0 ≤ (1 - p 1) / 2)
  rw [← wedge_iff]
  constructor
  · rintro ⟨_, hs, hw⟩
    exact ⟨hw, by linarith⟩
  · rintro ⟨hw, hs⟩
    have hp : 0 ≤ p 1 := (mul_nonneg_iff_of_pos_left c0_pos).mp
      ((abs_nonneg (p 0)).trans hw)
    exact ⟨hp, by linarith, hw⟩

lemma labelMap_coefficientBaseDomain :
    labelMap '' coefficientBaseDomain = SlopeRational.baseDomain := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (labelMap_coefficientBaseDomain_iff q).mp hq
  · intro hp
    refine ⟨inverseLabelMap p, ?_, labelMap_inverseLabelMap p⟩
    apply (labelMap_coefficientBaseDomain_iff _).mpr
    simpa only [labelMap_inverseLabelMap] using hp

lemma coefficientBaseDomain_area : volume.real coefficientBaseDomain = c0 := by
  have h := CostTransfer.labelMap_integral coefficientBaseDomain
    coefficientBaseDomain_measurable (fun _ : Plane => (1 : ℝ))
  rw [labelMap_coefficientBaseDomain] at h
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one] at h
  change volume.real SlopeRational.baseDomain =
    ell / 2 * volume.real coefficientBaseDomain at h
  rw [RationalEnergy.baseDomain_volume] at h
  have he := ell_mul_c0
  nlinarith [ell_pos]

lemma energyDensity_dictionary {d0 : ℝ} (hd : 0 < d0) {p : Plane}
    (hp : p ∈ coefficientBaseDomain) :
    v1 d0 (p 0) (p 1) ^ 2 + v2 d0 (p 0) (p 1) ^ 2 =
      (16 * (1 + d0) ^ 2) * SlopeRational.energyDensity (d0 / 2) (labelMap p) := by
  have h := squared_slope_dictionary
    (ne_of_gt (add_pos_of_nonneg_of_pos hp.1 hd)) 1 (p 0)
  rw [c0_sq] at h
  norm_num [centeredTilt, SlopeRational.energyDensity, labelMap, vec2, mul_pow] at h ⊢
  exact h.symm

lemma energy_dictionary {d0 : ℝ} (hd : 0 < d0) :
    uncenteredEnergy d0 = (32 * (1 + d0) ^ 2 / ell) *
      SlopeRational.energyIntegral (d0 / 2) := by
  have hi : (∫ p in coefficientBaseDomain,
      v1 d0 (p 0) (p 1) ^ 2 + v2 d0 (p 0) (p 1) ^ 2) =
      (16 * (1 + d0) ^ 2) * ∫ p in coefficientBaseDomain,
        SlopeRational.energyDensity (d0 / 2) (labelMap p) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun coefficientBaseDomain_measurable
      (fun p hp => energyDensity_dictionary hd hp)
  unfold uncenteredEnergy SlopeRational.energyIntegral
  rw [hi, ← labelMap_coefficientBaseDomain,
    CostTransfer.labelMap_integral _ coefficientBaseDomain_measurable]
  field_simp [ell_ne_zero]
  ring

lemma ceiling_dictionary_integral {d0 : ℝ} (hd : 0 < d0) :
    uncenteredCeiling d0 = (32 * (1 + d0) ^ 2 / ell) *
      SlopeRational.ceilingIntegral (d0 / 2) := by
  have hd1 : 1 + d0 ≠ 0 := by positivity
  have he : ell * c0 = (1 / 4 : ℝ) := ell_mul_c0
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun y : ℝ => SlopeRational.ceilingPolynomial (d0 / 2) y) ell
    (a := -c0) (b := c0)
  simp only [smul_eq_mul, mul_neg, he] at h
  have hi : (∫ u in (-c0)..c0,
      SlopeRational.ceilingPolynomial (d0 / 2) (ell * u)) =
      (1 / (32 * (1 + d0) ^ 2)) * uncenteredCeiling d0 := by
    simp_rw [ceiling_dictionary hd1, div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const]
    unfold uncenteredCeiling
    ring
  rw [hi] at h
  unfold SlopeRational.ceilingIntegral
  simp only [neg_div]
  rw [← h]
  field_simp [ell_ne_zero, hd1]

lemma half_tendsto_right :
    Tendsto (fun d : ℝ => d / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun d : ℝ => d / 2) 0 := by fun_prop
    simpa only [zero_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with d hd
    change 0 < d / 2
    exact div_pos hd (by norm_num)

lemma coefficientFactor_tendsto :
    Tendsto (fun d : ℝ => 32 * (1 + d) ^ 2 / ell)
      (𝓝[>] (0 : ℝ)) (𝓝 (32 / ell)) := by
  have hc : ContinuousAt (fun d : ℝ => 32 * (1 + d) ^ 2 / ell) 0 := by fun_prop
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

lemma c0_cube : c0 ^ 3 = c0 / 2 := by
  calc
    c0 ^ 3 = c0 * c0 ^ 2 := by ring
    _ = c0 / 2 := by rw [c0_sq]; ring

lemma c0_fifth : c0 ^ 5 = c0 / 4 := by
  calc
    c0 ^ 5 = c0 * (c0 ^ 2) ^ 2 := by ring
    _ = c0 / 4 := by rw [c0_sq]; ring

lemma uncenteredEnergy_tendsto :
    Tendsto uncenteredEnergy (𝓝[>] (0 : ℝ))
      (𝓝 (c0 ^ 3 / 6 + 7 * c0 ^ 5 / 30)) := by
  have h := coefficientFactor_tendsto.mul
    (SlopeRational.energyIntegral_tendsto.comp half_tendsto_right)
  have hc : (32 / ell) * (17 / 15360 : ℝ) =
      c0 ^ 3 / 6 + 7 * c0 ^ 5 / 30 := by
    rw [c0_cube, c0_fifth]
    field_simp [ell_ne_zero]
    nlinarith [ell_mul_c0]
  rw [hc] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (energy_dictionary hd).symm

lemma uncenteredCeiling_tendsto :
    Tendsto uncenteredCeiling (𝓝[>] (0 : ℝ)) (𝓝 (8 * c0 ^ 5 / 15)) := by
  have h := coefficientFactor_tendsto.mul
    (SlopeRational.ceilingIntegral_tendsto_zero_right.comp half_tendsto_right)
  have hc : (32 / ell) * (16 / 15360 : ℝ) = 8 * c0 ^ 5 / 15 := by
    rw [c0_fifth]
    field_simp [ell_ne_zero]
    nlinarith [ell_mul_c0]
  rw [hc] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (ceiling_dictionary_integral hd).symm

lemma coefficientGap_tendsto :
    Tendsto coefficientGap (𝓝[>] (0 : ℝ)) (𝓝 (c0 ^ 3 / 60)) := by
  have h := uncenteredEnergy_tendsto.sub uncenteredCeiling_tendsto
  have hc : c0 ^ 3 / 6 + 7 * c0 ^ 5 / 30 - 8 * c0 ^ 5 / 15 =
      c0 ^ 3 / 60 := by rw [c0_cube, c0_fifth]; ring
  exact hc ▸ h

lemma exists_positive_coefficientGap : ∃ d0 : ℝ, 0 < d0 ∧ 0 < coefficientGap d0 := by
  have hp : 0 < c0 ^ 3 / 60 := by have hc := c0_pos; positivity
  have h := coefficientGap_tendsto.eventually (eventually_gt_nhds hp)
  have hd : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), 0 < d := self_mem_nhdsWithin
  obtain ⟨d, hd, hgap⟩ := (hd.and h).exists
  exact ⟨d, hd, hgap⟩

theorem coefficient_limits : CoefficientLimitsStatement :=
  ⟨uncenteredEnergy_tendsto, uncenteredCeiling_tendsto,
    coefficientGap_tendsto, exists_positive_coefficientGap⟩

end RationalDictionary

end

end OAI
