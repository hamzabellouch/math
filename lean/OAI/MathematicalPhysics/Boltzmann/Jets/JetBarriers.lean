import OAI.MathematicalPhysics.Boltzmann.Branching.DatumBounds
import OAI.MathematicalPhysics.Boltzmann.Branching.GainNonnegative
import OAI.MathematicalPhysics.Boltzmann.Branching.HotGainReduction
import OAI.MathematicalPhysics.Boltzmann.Branching.LossIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.PlaneChart
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianFrequency
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetGain
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import Mathlib.Analysis.Calculus.Rademacher

namespace OAI

section

/-! # The actual unshifted cold-jet density and its mass bound -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetPrototype

abbrev Space := Transverse × ℝ
abbrev Phase := Space × Velocity

abbrev spaceVolume : Measure Space := volume.prod volume

def sign (positive : Bool) : ℝ := if positive then 1 else -1

def center (α γ s : ℝ) (positive : Bool) (z : ℝ) : Velocity :=
  PlaneChart.join 0 (AxialFlow.profile (sign positive) α γ s z)

def axialAmplitude (K γ s : ℝ) (z : ℝ) : ℝ :=
  (Ioo (-(1 / 8 : ℝ)) (1 / 8)).indicator (fun z => (K / s) * S (γ * z / s)) z

def spatial (η K γ s : ℝ) (positive : Bool) (x : Space) : ℝ :=
  (mask η s positive).indicator (fun _ => (1 : ℝ)) x.1 * axialAmplitude K γ s x.2

def density (η K α γ s d : ℝ) (positive : Bool) (p : Phase) : ℝ :=
  spatial η K γ s positive p.1 * JetThermalLaw.density d (center α γ s positive p.1.2) p.2

theorem axialAmplitude_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (γ z : ℝ) :
    0 ≤ axialAmplitude K γ s z := by
  apply indicator_nonneg
  intro z _
  exact mul_nonneg (div_nonneg hK hs) (S_pos _).le

theorem spatial_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (η γ : ℝ) (a : Bool) (x : Space) :
    0 ≤ spatial η K γ s a x :=
  mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
    (axialAmplitude_nonneg hK hs γ _)

theorem density_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ : ℝ) (a : Bool) (p : Phase) : 0 ≤ density η K α γ s d a p :=
  mul_nonneg (spatial_nonneg hK hs η γ a _)
    (JetThermalLaw.density_nonneg hd _ _)

theorem axialAmplitude_integrable (K γ s : ℝ) : Integrable (axialAmplitude K γ s) := by
  apply integrable_indicator_iff measurableSet_Ioo |>.mpr
  exact (((continuous_const.mul (continuous_S.comp
    ((continuous_const.mul continuous_id).div_const s))).integrableOn_Icc).mono_set Ioo_subset_Icc_self)

theorem spatial_integrable {η : ℝ} (hη : 0 ≤ η) (K γ s : ℝ) (a : Bool) :
    Integrable (spatial η K γ s a) spaceVolume :=
  (indicator_integrable hη a).mul_prod (axialAmplitude_integrable K γ s)

theorem measurable_spatial (η K γ s : ℝ) (a : Bool) : Measurable (spatial η K γ s a) := by
  unfold spatial axialAmplitude
  exact (((measurable_const.indicator (measurableSet_mask η s a)).comp measurable_fst).mul
    (((continuous_const.mul (continuous_S.comp
      ((continuous_const.mul continuous_id).div_const s))).measurable.indicator measurableSet_Ioo).comp
      measurable_snd))

theorem measurable_center (α γ s : ℝ) (a : Bool) : Measurable (center α γ s a) := by
  change Measurable (fun z => SheetMeasures.join (0, AxialFlow.profile (sign a) α γ s z))
  exact SheetMeasures.join.measurable.comp
    (measurable_const.prodMk (AxialFlow.continuous_profile _ _ _ _).measurable)

theorem measurable_density (η K α γ s d : ℝ) (a : Bool) :
    Measurable (density η K α γ s d a) := by
  unfold density JetThermalLaw.density JetThermalLaw.scaled
  have hc : Measurable (fun p : Phase => center α γ s a p.1.2) :=
    (measurable_center α γ s a).comp (measurable_snd.comp measurable_fst)
  have hv : Measurable (fun p : Phase => d⁻¹ • (p.2 - center α γ s a p.1.2)) :=
    (measurable_const : Measurable (fun _ : Phase => d⁻¹)).smul (measurable_snd.sub hc)
  exact ((measurable_spatial η K γ s a).comp measurable_fst).mul
    (measurable_const.mul (JetThermalKernel.J_smooth.continuous.measurable.comp
      hv))

theorem density_velocity_integral {d : ℝ} (hd : 0 < d)
    (η K α γ s : ℝ) (a : Bool) (x : Space) :
    (∫ v, density η K α γ s d a (x, v)) = spatial η K γ s a x := by
  simp only [density, integral_const_mul, JetThermalLaw.density_mass hd, mul_one]

theorem density_integrable {η K s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hs : 0 ≤ s) (hd : 0 < d) (α γ : ℝ) (a : Bool) :
    Integrable (density η K α γ s d a) (spaceVolume.prod volume) := by
  apply (integrable_prod_iff (measurable_density η K α γ s d a).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    exact (JetThermalLaw.density_integrable hd (center α γ s a x.2)).const_mul
      (spatial η K γ s a x)
  · have he : (fun x : Space => ∫ v, ‖density η K α γ s d a (x, v)‖) =
        spatial η K γ s a := by
      funext x
      simp_rw [Real.norm_of_nonneg (density_nonneg hK hs hd.le η α γ a _)]
      exact density_velocity_integral hd η K α γ s a x
    rw [he]
    exact spatial_integrable hη K γ s a

theorem density_mass_eq {η K s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hs : 0 ≤ s) (hd : 0 < d) (α γ : ℝ) (a : Bool) :
    (∫ p, density η K α γ s d a p ∂spaceVolume.prod volume) =
      volume.real (mask η s a) * ((K / s) *
        ∫ z in Ioo (-(1 / 8 : ℝ)) (1 / 8), S (γ * z / s)) := by
  rw [integral_prod _ (density_integrable hη hK hs hd α γ a)]
  simp_rw [density_velocity_integral hd]
  unfold spatial spaceVolume
  rw [integral_prod_mul, integral_indicator (measurableSet_mask η s a), setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  unfold axialAmplitude
  rw [integral_indicator measurableSet_Ioo, integral_const_mul]

theorem density_mass_bound {η K γ s d : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    (∫ p, density η K α γ s d a p ∂spaceVolume.prod volume) ≤
      (8 * Real.pi * K / γ) * s ^ 2 := by
  rw [density_mass_eq hη hK hs.le hd]
  have hz : (∫ z in Ioo (-(1 / 8 : ℝ)) (1 / 8), S (γ * z / s)) ≤ 2 * s / γ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num :
      -(1 / 8 : ℝ) ≤ 1 / 8)]
    exact scaled_intervalIntegral_le hγ hs _ _
  have hm := mul_le_mul_of_nonneg_left hz (div_nonneg hK hs.le)
  have ha := mask_area_uniform hη hηmax hs.le a
  calc
    _ ≤ volume.real (mask η s a) * ((K / s) * (2 * s / γ)) :=
      mul_le_mul_of_nonneg_left hm measureReal_nonneg
    _ ≤ (4 * Real.pi * s ^ 2) * ((K / s) * (2 * s / γ)) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := by field_simp; ring

end BoltzmannNonuniqueness.JetPrototype

end

end

section

/-! # Absolute entropy of the cold datum's spatial factor -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight
open BoltzmannNonuniqueness.JetAxialEntropy
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure

namespace BoltzmannNonuniqueness.JetSpatialEntropy

theorem scalar_scaled_integrable {f : ℝ → ℝ} (hf : Integrable f) {γ s : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) : Integrable (fun z => f (γ * z / s)) := by
  have h := hf.comp_mul_left' (div_ne_zero hγ.ne' hs.ne')
  convert h using 1
  funext z
  congr 1
  ring

theorem scalar_scaled_integral (f : ℝ → ℝ) {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) :
    (∫ z, f (γ * z / s)) = (s / γ) * ∫ z, f z := by
  have he : (fun z => f (γ * z / s)) = fun z => f ((γ / s) * z) := by
    funext z
    congr 1
    ring
  rw [he, Measure.integral_comp_mul_left, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (div_pos hγ hs)), inv_div]

def massConstant : ℝ := ∫ z, S z

def entropyConstant : ℝ := ∫ z, entropy (S z)

theorem massConstant_nonneg : 0 ≤ massConstant := integral_nonneg (fun z => (S_pos z).le)

theorem entropyConstant_nonneg : 0 ≤ entropyConstant :=
  integral_nonneg (fun z => entropy_nonneg (S_pos z).le)

def axialMajorant (K γ s z : ℝ) : ℝ :=
  S (γ * z / s) * entropy (K / s) + (K / s) * entropy (S (γ * z / s))

theorem axial_entropy_bound {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (γ z : ℝ) :
    entropy (axialAmplitude K γ s z) ≤ axialMajorant K γ s z := by
  by_cases hz : z ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
  · rw [axialAmplitude, indicator_of_mem hz]
    exact entropy_mul_le (div_nonneg hK hs.le) (S_pos _).le
  · rw [axialAmplitude, indicator_of_notMem hz]
    simp only [entropy, zero_mul]
    exact add_nonneg (mul_nonneg (S_pos _).le (entropy_nonneg (div_nonneg hK hs.le)))
      (mul_nonneg (div_nonneg hK hs.le) (entropy_nonneg (S_pos _).le))

theorem axialMajorant_integrable {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (K : ℝ) :
    Integrable (axialMajorant K γ s) :=
  ((scalar_scaled_integrable integrable_S hγ hs).mul_const _).add
    ((scalar_scaled_integrable integrable_axial_entropy hγ hs).const_mul _)

theorem axial_entropy_integrable {K γ s : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) :
    Integrable (fun z => entropy (axialAmplitude K γ s z)) := by
  have he : (fun z => entropy (axialAmplitude K γ s z)) =
      (Ioo (-(1 / 8 : ℝ)) (1 / 8)).indicator (fun z => entropy ((K / s) * S (γ * z / s))) := by
    funext z
    by_cases hz : z ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simp only [axialAmplitude, indicator_of_mem hz]
    · simp only [axialAmplitude, indicator_of_notMem hz, entropy, zero_mul]
  apply (axialMajorant_integrable hγ hs K).mono'
  · rw [he]
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ measurableSet_Ioo
    exact (continuous_entropy_comp (continuous_const.mul (continuous_S.comp
      ((continuous_const.mul continuous_id).div_const s)))
        (fun z => mul_nonneg (div_nonneg hK hs.le) (S_pos _).le)).measurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (entropy_nonneg (axialAmplitude_nonneg hK hs.le γ z))]
    exact axial_entropy_bound hK hs γ z

theorem axial_entropy_integral {K γ s : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) :
    (∫ z, entropy (axialAmplitude K γ s z)) ≤
      (s / γ) * (entropy (K / s) * massConstant + (K / s) * entropyConstant) := by
  apply (integral_mono (axial_entropy_integrable hK hγ hs)
    (axialMajorant_integrable hγ hs K) (axial_entropy_bound hK hs γ)).trans_eq
  have hS : Integrable (fun z => S (γ * z / s)) := scalar_scaled_integrable integrable_S hγ hs
  have hE : Integrable (fun z => entropy (S (γ * z / s))) :=
    scalar_scaled_integrable integrable_axial_entropy hγ hs
  have hEI : (∫ z, entropy (S (γ * z / s))) =
      (s / γ) * ∫ z, entropy (S z) :=
    scalar_scaled_integral (fun z => entropy (S z)) hγ hs
  unfold axialMajorant
  rw [integral_add (hS.mul_const _) (hE.const_mul _),
    integral_mul_const, integral_const_mul, scalar_scaled_integral _ hγ hs, hEI]
  unfold massConstant entropyConstant
  ring

theorem spatial_entropy_eq (η K γ s : ℝ) (a : Bool) :
    (fun x : Space => entropy (spatial η K γ s a x)) =
      fun x => (mask η s a).indicator (fun _ => (1 : ℝ)) x.1 *
        entropy (axialAmplitude K γ s x.2) := by
  funext x
  by_cases hx : x.1 ∈ mask η s a <;> simp [spatial, hx, entropy]

theorem spatial_entropy_integrable {η K γ s : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    Integrable (fun x : Space => entropy (spatial η K γ s a x)) spaceVolume := by
  rw [spatial_entropy_eq]
  exact (indicator_integrable hη a).mul_prod (axial_entropy_integrable hK hγ hs)

theorem spatial_entropy_integral {η K γ s : ℝ} (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x : Space, entropy (spatial η K γ s a x) ∂spaceVolume) ≤
      volume.real (mask η s a) * (s / γ) *
        (entropy (K / s) * massConstant + (K / s) * entropyConstant) := by
  rw [spatial_entropy_eq]
  dsimp only [spaceVolume]
  rw [integral_prod_mul ((mask η s a).indicator (fun _ => (1 : ℝ)))
    (fun z => entropy (axialAmplitude K γ s z)), integral_indicator (measurableSet_mask η s a),
    setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  have h := mul_le_mul_of_nonneg_left (axial_entropy_integral hK hγ hs)
    (measureReal_nonneg : 0 ≤ volume.real (mask η s a))
  simpa only [mul_assoc] using h

end BoltzmannNonuniqueness.JetSpatialEntropy

end

end

section

/-! # Velocity support and spatial confinement of the free cold cores -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetSupport

theorem center_norm (α γ s : ℝ) (a : Bool) (z : ℝ) :
    ‖center α γ s a z‖ = |AxialFlow.profile (sign a) α γ s z| := by
  have h := PlaneChart.norm_join_sq (0 : Transverse) (AxialFlow.profile (sign a) α γ s z)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  change ‖center α γ s a z‖ ^ 2 = _ at h
  nlinarith [sq_abs (AxialFlow.profile (sign a) α γ s z), norm_nonneg (center α γ s a z),
    abs_nonneg (AxialFlow.profile (sign a) α γ s z)]

theorem abs_sign (a : Bool) : |sign a| = 1 := by cases a <;> norm_num [sign]

theorem center_norm_bound {α : ℝ} (hα : 0 ≤ α) (γ s : ℝ) (a : Bool) (z : ℝ) :
    ‖center α γ s a z‖ ≤ 1 + α := by
  rw [center_norm]
  have h := AxialFlow.profile_sub_center_le (σ := sign a) (γ := γ) (s := s) (z := z) hα
  have ht := abs_add_le (AxialFlow.profile (sign a) α γ s z - sign a) (sign a)
  rw [sub_add_cancel, abs_sign] at ht
  linarith

theorem density_velocity_bound {d α : ℝ} (hd : 0 < d) (hα : 0 ≤ α)
    (η K γ s : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) : ‖p.2‖ < 1 + α + d := by
  have hthermal : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 :=
    right_ne_zero_of_mul hp
  exact (JetThermalLaw.density_velocity_bound hd hthermal).trans_le
    (add_le_add (center_norm_bound hα γ s a _) le_rfl)

theorem density_support_two {d α : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (η K γ s : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) : ‖p.2‖ < 2 := by
  have h := density_velocity_bound hd hα η K γ s a hp
  linarith

theorem initial_spatial_support (η K α γ s d : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    p.1.1 ∈ mask η s a ∧ |p.1.2| < 1 / 8 := by
  have hsp : spatial η K γ s a p.1 ≠ 0 := left_ne_zero_of_mul hp
  have hm : (mask η s a).indicator (fun _ => (1 : ℝ)) p.1.1 ≠ 0 := left_ne_zero_of_mul hsp
  have hz : axialAmplitude K γ s p.1.2 ≠ 0 := right_ne_zero_of_mul hsp
  have hy : p.1.1 ∈ mask η s a := by
    by_contra h
    exact hm (indicator_of_notMem h _)
  have hz' : p.1.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8) := by
    by_contra h
    exact hz (indicator_of_notMem h _)
  exact ⟨hy, abs_lt.mpr hz'⟩

theorem transverse_velocity_bound {d : ℝ} (hd : 0 < d) (η K α γ s : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    ‖transverse p.2‖ < d := by
  have hthermal : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 :=
    right_ne_zero_of_mul hp
  have hdist : ‖p.2 - center α γ s a p.1.2‖ < d :=
    lt_of_not_ge (fun h => hthermal (JetThermalLaw.density_zero hd _ _ h))
  have hn := norm_sq_split (p.2 - center α γ s a p.1.2)
  have he : transverse (p.2 - center α γ s a p.1.2) = transverse p.2 := by
    rw [PlaneChart.transverse_sub, JetPrototype.center, PlaneChart.transverse_join, sub_zero]
  rw [he] at hn
  have hle : ‖transverse p.2‖ ≤ ‖p.2 - center α γ s a p.1.2‖ := by
    nlinarith [norm_nonneg (transverse p.2), norm_nonneg (p.2 - center α γ s a p.1.2),
      sq_nonneg (axial (p.2 - center α γ s a p.1.2))]
  exact hle.trans_lt hdist

/-- A free core remains in the transverse enlargement once `t d ≤ δ_s`. -/
theorem free_core_transverse {t d η s : ℝ} (ht : 0 ≤ t) (hd : 0 < d)
    (hwidth : t * d ≤ enlargementWidth η s) (K α γ : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    p.1.1 + t • transverse p.2 ∈ enlargement η s a := by
  have hmask := (initial_spatial_support η K α γ s d a hp).1
  apply mem_cthickening_of_dist_le _ p.1.1 _ _ hmask
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left (transverse_velocity_bound hd η K α γ s a hp).le ht).trans hwidth

/-- Axial free flight stays inside the manuscript's interval enlargement. -/
theorem free_core_axial {t d α : ℝ} (ht : 0 ≤ t) (hd : 0 < d) (hdmax : d ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (η K γ s : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    |p.1.2 + t * axial p.2| ≤ 1 / 8 + 2 * t + 1 / 16 := by
  have hz := (initial_spatial_support η K α γ s d a hp).2
  have hv := density_support_two hd hdmax hα hαmax η K γ s a hp
  have hn := norm_sq_split p.2
  have ha : |axial p.2| ≤ ‖p.2‖ := by
    nlinarith [sq_abs (axial p.2), abs_nonneg (axial p.2), norm_nonneg p.2,
      sq_nonneg ‖transverse p.2‖]
  have htri := abs_add_le p.1.2 (t * axial p.2)
  rw [abs_mul, abs_of_nonneg ht] at htri
  have htime := mul_le_mul_of_nonneg_left (ha.trans hv.le) ht
  linarith

end BoltzmannNonuniqueness.JetSupport

end

end

section

/-! # Thermal and distance bounds on actual free cold-core flights -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCoreFlight

def axialCenter (α γ s t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  AxialFlow.velocity (sign a) α γ s t (p.1.2 + t * axial p.2)

def error (α γ s t : ℝ) (a : Bool) (p : JetPrototype.Phase) : Velocity :=
  p.2 - PlaneChart.join 0 (axialCenter α γ s t a p)

theorem norm_sq_error (v : Velocity) (u : ℝ) :
    ‖v - PlaneChart.join 0 u‖ ^ 2 = ‖transverse v‖ ^ 2 + (axial v - u) ^ 2 := by
  rw [norm_sq_split, PlaneChart.transverse_sub, PlaneChart.transverse_join,
    sub_zero, PlaneChart.axial_sub, PlaneChart.axial_join]

theorem axial_error_bound {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (a : Bool) (p : JetPrototype.Phase) :
    |axial p.2 - axialCenter α γ s t a p| ≤
      |axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2| := by
  apply AxialFlow.thermal_velocity_error hα hγ hs ht
  have he : p.1.2 + t * axial p.2 - t * axial p.2 = p.1.2 := by ring
  rw [he]
  ring

theorem error_le_initial {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (a : Bool) (p : JetPrototype.Phase) :
    ‖error α γ s t a p‖ ≤ ‖p.2 - center α γ s a p.1.2‖ := by
  have h := axial_error_bound hα hγ hs ht a p
  have hsquare : (axial p.2 - axialCenter α γ s t a p) ^ 2 ≤
      (axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2) ^ 2 := by
    nlinarith [sq_abs (axial p.2 - axialCenter α γ s t a p),
      sq_abs (axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2),
      abs_nonneg (axial p.2 - axialCenter α γ s t a p)]
  have hn₁ := norm_sq_error p.2 (axialCenter α γ s t a p)
  have hn₂ := norm_sq_error p.2 (AxialFlow.profile (sign a) α γ s p.1.2)
  change ‖error α γ s t a p‖ ^ 2 = _ at hn₁
  change ‖p.2 - center α γ s a p.1.2‖ ^ 2 = _ at hn₂
  nlinarith [norm_nonneg (error α γ s t a p), norm_nonneg (p.2 - center α γ s a p.1.2)]

theorem error_lt_width {d α γ s t : ℝ} (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : density η K α γ s d a p ≠ 0) : ‖error α γ s t a p‖ < d := by
  apply (error_le_initial hα hγ hs ht a p).trans_lt
  have hh : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 := right_ne_zero_of_mul hp
  exact lt_of_not_ge (fun h => hh (JetThermalLaw.density_zero hd _ _ h))

theorem transverse_distance_bound {t : ℝ} (ht : 0 ≤ t) (η K α γ s d : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : density η K α γ s d a p ≠ 0) :
    infDist (p.1.1 + t • transverse p.2) (JetGeometry.mask η s a) ≤ t * ‖transverse p.2‖ := by
  have h := infDist_le_dist_of_mem (JetSupport.initial_spatial_support η K α γ s d a hp).1
    (x := p.1.1 + t • transverse p.2)
  simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht] using h

theorem axial_distance_bound {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (η K d : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : density η K α γ s d a p ≠ 0) :
    infDist (AxialFlow.foot (sign a) α γ s t (p.1.2 + t * axial p.2)) (Icc (-(1 / 8 : ℝ)) (1 / 8)) ≤
      t * |axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2| := by
  have hz := (JetSupport.initial_spatial_support η K α γ s d a hp).2
  have hmem : p.1.2 ∈ Icc (-(1 / 8 : ℝ)) (1 / 8) :=
    ⟨(abs_lt.mp hz).1.le, (abs_lt.mp hz).2.le⟩
  have hdist := infDist_le_dist_of_mem hmem
    (x := AxialFlow.foot (sign a) α γ s t (p.1.2 + t * axial p.2))
  rw [Real.dist_eq] at hdist
  apply hdist.trans
  have h := AxialFlow.free_flight_foot_error (σ := sign a) (z := p.1.2)
    (δ := axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2) hα hγ hs ht
  simpa only [add_sub_cancel] using h

theorem distance_square_bound {d α γ s t : ℝ} (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : density η K α γ s d a p ≠ 0) :
    infDist (p.1.1 + t • transverse p.2) (JetGeometry.mask η s a) ^ 2 +
      infDist (AxialFlow.foot (sign a) α γ s t (p.1.2 + t * axial p.2))
        (Icc (-(1 / 8 : ℝ)) (1 / 8)) ^ 2 ≤ t ^ 2 * d ^ 2 := by
  have hy := transverse_distance_bound ht η K α γ s d a hp
  have hz := axial_distance_bound hα hγ hs ht η K d a hp
  have hy2 : infDist (p.1.1 + t • transverse p.2) (JetGeometry.mask η s a) ^ 2 ≤
      (t * ‖transverse p.2‖) ^ 2 := by
    gcongr
    exact infDist_nonneg
  have hz2 : infDist (AxialFlow.foot (sign a) α γ s t (p.1.2 + t * axial p.2))
      (Icc (-(1 / 8 : ℝ)) (1 / 8)) ^ 2 ≤
      (t * |axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2|) ^ 2 := by
    gcongr
    exact infDist_nonneg
  have hh : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 := right_ne_zero_of_mul hp
  have hn : ‖p.2 - center α γ s a p.1.2‖ < d :=
    lt_of_not_ge (fun h => hh (JetThermalLaw.density_zero hd _ _ h))
  have hsquare := norm_sq_error p.2 (AxialFlow.profile (sign a) α γ s p.1.2)
  change ‖p.2 - center α γ s a p.1.2‖ ^ 2 = _ at hsquare
  have hi : ‖transverse p.2‖ ^ 2 +
      (axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2) ^ 2 ≤ d ^ 2 := by
    nlinarith [norm_nonneg (p.2 - center α γ s a p.1.2)]
  have hf := mul_le_mul_of_nonneg_left hi (sq_nonneg t)
  rw [mul_pow, sq_abs] at hz2
  nlinarith only [hy2, hz2, hf]

end BoltzmannNonuniqueness.JetCoreFlight

end

end

section

/-! # The actual Gaussian barrier and free-core domination -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetAxialWeight
open BoltzmannNonuniqueness.JetCoreFlight

namespace BoltzmannNonuniqueness.JetBarrier

def centerVelocity (α γ s t : ℝ) (a : Bool) (x : Space) : Velocity :=
  PlaneChart.join 0 (AxialFlow.velocity (sign a) α γ s t x.2)

def distanceSquared (η α γ s t : ℝ) (a : Bool) (x : Space) : ℝ :=
  infDist x.1 (JetGeometry.mask η s a) ^ 2 +
    infDist (AxialFlow.foot (sign a) α γ s t x.2) (Icc (-(1 / 8 : ℝ)) (1 / 8)) ^ 2

def flight (t : ℝ) (p : JetPrototype.Phase) : JetPrototype.Phase :=
  ((p.1.1 + t • transverse p.2, p.1.2 + t * axial p.2), p.2)

def exponent (η α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  t - (2 - t) * ‖p.2 - centerVelocity α γ s t a p.1‖ ^ 2 / d ^ 2 -
    (1 / 8 : ℝ) * distanceSquared η α γ s t a p.1 / (d ^ 2 * t)

def barrier (η K α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹ *
    Real.exp (exponent η α γ s d t a p)

theorem spatial_le {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (η γ : ℝ) (a : Bool) (x : Space) :
    spatial η K γ s a x ≤ K / s := by
  by_cases hy : x.1 ∈ JetGeometry.mask η s a
  · by_cases hz : x.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simpa only [spatial, axialAmplitude, indicator_of_mem hy, indicator_of_mem hz, one_mul] using
        mul_le_of_le_one_right (div_nonneg hK hs.le) (S_le_one (γ * x.2 / s))
    · simp only [spatial, axialAmplitude, indicator_of_notMem hz, mul_zero]
      exact div_nonneg hK hs.le
  · simp only [spatial, indicator_of_notMem hy, zero_mul]
    exact div_nonneg hK hs.le

theorem initial_density_bound {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 ≤ d)
    (η α γ : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    density η K α γ s d a p ≤ (K / s) * (d ^ 3)⁻¹ * JetThermalKernel.bound := by
  calc
    _ ≤ (K / s) * JetThermalLaw.density d (center α γ s a p.1.2) p.2 :=
      mul_le_mul_of_nonneg_right (spatial_le hK hs η γ a p.1) (JetThermalLaw.density_nonneg hd _ _)
    _ ≤ (K / s) * ((d ^ 3)⁻¹ * JetThermalKernel.bound) :=
      mul_le_mul_of_nonneg_left (JetThermalLaw.density_le hd _ _) (div_nonneg hK hs.le)
    _ = _ := by ring

theorem flight_exponent_lower {d α γ s t : ℝ} (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 < t) (htmax : t ≤ 2) (η K : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : density η K α γ s d a p ≠ 0) : -3 ≤ exponent η α γ s d t a (flight t p) := by
  have hr := error_lt_width hd hα hγ hs ht.le η K a hp
  have hp2 := distance_square_bound hd hα hγ hs ht.le η K a hp
  have hr2 : ‖error α γ s t a p‖ ^ 2 ≤ d ^ 2 := by
    nlinarith [norm_nonneg (error α γ s t a p)]
  have hk : (2 - t) * ‖error α γ s t a p‖ ^ 2 / d ^ 2 ≤ 2 - t := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    exact mul_le_mul_of_nonneg_left hr2 (sub_nonneg.mpr htmax)
  have hx : (1 / 8 : ℝ) * distanceSquared η α γ s t a (flight t p).1 / (d ^ 2 * t) ≤ t / 8 := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hd) ht)).mpr
    change (1 / 8 : ℝ) * (_ + _) ≤ _
    dsimp only [flight]
    nlinarith only [hp2]
  change -3 ≤ t - (2 - t) * ‖error α γ s t a p‖ ^ 2 / d ^ 2 - _
  nlinarith only [hk, hx, ht]

theorem barrier_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ t : ℝ) (a : Bool) (p : JetPrototype.Phase) : 0 ≤ barrier η K α γ s d t a p := by
  unfold barrier
  have := JetThermalKernel.bound_pos
  positivity

theorem free_core_le_barrier {K d α γ s t : ℝ} (hK : 0 ≤ K) (hd : 0 < d) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 < t) (htmax : t ≤ 2)
    (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    density η K α γ s d a p ≤ barrier η K α γ s d t a (flight t p) := by
  by_cases hp : density η K α γ s d a p = 0
  · rw [hp]
    exact barrier_nonneg hK hs.le hd.le η α γ t a _
  have he := Real.exp_le_exp.mpr (flight_exponent_lower hd hα hγ hs ht htmax η K a hp)
  have hc : 0 ≤ (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹ := by
    have := JetThermalKernel.bound_pos
    positivity
  calc
    _ ≤ (K / s) * (d ^ 3)⁻¹ * JetThermalKernel.bound := initial_density_bound hK hs hd.le η α γ a p
    _ = (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹ * Real.exp (-3) := by
      have hx : Real.exp (3 : ℝ) * Real.exp (-3) = 1 := by rw [← Real.exp_add]; norm_num
      calc
        _ = ((K / s) * (d ^ 3)⁻¹ * JetThermalKernel.bound) *
            (Real.exp 3 * Real.exp (-3)) := by rw [hx, mul_one]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he hc

end BoltzmannNonuniqueness.JetBarrier

end

end

section

/-! # Self-collision and the uniform loss-frequency bound of the actual barrier -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetBarrierCollision

def massScale (η K α γ s d t : ℝ) (a : Bool) (x : Space) : ℝ :=
  (Real.exp 3 * JetThermalKernel.bound) * (K / s) *
    Real.exp (t - (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t))

theorem massScale_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s)
    (η α γ d t : ℝ) (a : Bool) (x : Space) : 0 ≤ massScale η K α γ s d t a x := by
  unfold massScale
  have := JetThermalKernel.bound_pos
  positivity

theorem barrier_eq_density {d : ℝ} (hd : 0 < d)
    (η K α γ s t : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    barrier η K α γ s d t a (x, v) =
      GaussianFrequency.density (massScale η K α γ s d t a x) (2 - t) d
        (centerVelocity α γ s t a x) v := by
  rw [GaussianFrequency.density_eq_gaussian hd]
  unfold barrier exponent gaussian massScale
  have he : t - (2 - t) * ‖v - centerVelocity α γ s t a x‖ ^ 2 / d ^ 2 -
      (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t) =
      (t - (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t)) +
      (-( (2 - t) / d ^ 2) * ‖v - centerVelocity α γ s t a x‖ ^ 2) := by ring
  dsimp only
  rw [he, Real.exp_add]
  ring

theorem measurable_velocity {d : ℝ} (hd : 0 < d)
    (η K α γ s t : ℝ) (a : Bool) (x : Space) :
    Measurable (fun v => barrier η K α γ s d t a (x, v)) := by
  simp_rw [barrier_eq_density hd, GaussianFrequency.density_eq_gaussian hd]
  unfold gaussian
  fun_prop

theorem integrable_gain {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    Integrable (GainOrder.integrand (fun w => barrier η K α γ s d t a (x, w)) v)
      ((volume : Measure Velocity).prod sphereArea) := by
  have hb : 0 < 2 - t := by linarith
  simpa only [GainOrder.integrand, barrier_eq_density hd] using
    GainOrder.integrable_normalizedGaussian (massScale_nonneg hK hs η α γ d t a x) hb hd
      (centerVelocity α γ s t a x) v

theorem massScale_le {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) :
    massScale η K α γ s d t a x ≤ Real.exp 4 * JetThermalKernel.bound * (K / s) := by
  have hD : 0 ≤ distanceSquared η α γ s t a x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he : t - (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t) ≤ 1 := by
    have : 0 ≤ (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t) := by positivity
    linarith
  have hc : 0 ≤ Real.exp 3 * JetThermalKernel.bound * (K / s) := by
    have := JetThermalKernel.bound_pos
    positivity
  calc
    _ ≤ (Real.exp 3 * JetThermalKernel.bound) * (K / s) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hc
    _ = _ := by
      have he4 : Real.exp (3 : ℝ) * Real.exp 1 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
      calc
        _ = (Real.exp 3 * Real.exp 1) * JetThermalKernel.bound * (K / s) := by ring
        _ = _ := by rw [he4]

def frequencyConstant : ℝ :=
  2 * Real.pi * Real.exp 4 * JetThermalKernel.bound *
    (JetGaussianMoments.mass + JetGaussianMoments.moment)

theorem frequencyConstant_nonneg : 0 ≤ frequencyConstant := by
  unfold frequencyConstant
  have := JetGaussianMoments.mass_nonneg
  have := JetGaussianMoments.moment_nonneg
  have := JetThermalKernel.bound_pos
  positivity

/-- The constant is independent of the jet label, thermal width and position. -/
theorem frequency_bound {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space)
    (z : Position) (v : Velocity) :
    frequency (fun p => barrier η K α γ s d t a (x, p.2)) z v ≤
      frequencyConstant * (K / s) * (d + ‖v - centerVelocity α γ s t a x‖) := by
  have hc := massScale_nonneg hK hs η α γ d t a x
  have hcle := massScale_le hK hs hd ht htmax η α γ a x
  have hb : 1 ≤ 2 - t := by linarith
  simp_rw [barrier_eq_density hd]
  have hf := GaussianFrequency.frequency_le hc hb hd (centerVelocity α γ s t a x) v z
  have hlinear : JetGaussianMoments.mass * ‖v - centerVelocity α γ s t a x‖ +
      JetGaussianMoments.moment * d ≤
      (JetGaussianMoments.mass + JetGaussianMoments.moment) *
        (d + ‖v - centerVelocity α γ s t a x‖) := by
    nlinarith [mul_nonneg JetGaussianMoments.mass_nonneg hd.le,
      mul_nonneg JetGaussianMoments.moment_nonneg (norm_nonneg (v - centerVelocity α γ s t a x))]
  calc
    _ ≤ _ := hf
    _ ≤ 2 * Real.pi * massScale η K α γ s d t a x *
        ((JetGaussianMoments.mass + JetGaussianMoments.moment) *
          (d + ‖v - centerVelocity α γ s t a x‖)) :=
      mul_le_mul_of_nonneg_left hlinear (mul_nonneg (by positivity) hc)
    _ ≤ 2 * Real.pi * (Real.exp 4 * JetThermalKernel.bound * (K / s)) *
        ((JetGaussianMoments.mass + JetGaussianMoments.moment) *
          (d + ‖v - centerVelocity α γ s t a x‖)) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcle (by positivity))
      exact mul_nonneg (add_nonneg JetGaussianMoments.mass_nonneg JetGaussianMoments.moment_nonneg)
        (add_nonneg hd.le (norm_nonneg _))
    _ = _ := by unfold frequencyConstant; ring

/-- The fixed-position barrier is a Maxwellian, so its gain equals its loss. -/
theorem self_gain {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) (z : Position) (v : Velocity) :
    gain (fun p => barrier η K α γ s d t a (x, p.2)) z v =
      barrier η K α γ s d t a (x, v) *
        frequency (fun p => barrier η K α γ s d t a (x, p.2)) z v := by
  let c := massScale η K α γ s d t a x
  let u := centerVelocity α γ s t a x
  have hb : 0 < 2 - t := by linarith
  have hc : 0 ≤ c := massScale_nonneg hK hs η α γ d t a x
  have hfun : (fun p : Phase => barrier η K α γ s d t a (x, p.2)) =
      fun p => gaussian (c * (d ^ 3)⁻¹) ((2 - t) / d ^ 2) u p.2 := by
    funext p
    rw [barrier_eq_density hd, GaussianFrequency.density_eq_gaussian hd]
  have hf : Integrable (gaussian (c * (d ^ 3)⁻¹) ((2 - t) / d ^ 2) u) := by
    change Integrable (fun w => gaussian (c * (d ^ 3)⁻¹) ((2 - t) / d ^ 2) u w)
    simpa only [GaussianFrequency.density_eq_gaussian hd] using
      (show Integrable (fun w => GaussianFrequency.density c (2 - t) d u w) from
        GaussianFrequency.integrable hb hd c u)
  have hm : Integrable (fun w => ‖w‖ * gaussian (c * (d ^ 3)⁻¹) ((2 - t) / d ^ 2) u w) := by
    simpa only [GaussianFrequency.density_eq_gaussian hd] using
      GaussianFrequency.first_moment_integrable hc hb hd u
  rw [hfun, barrier_eq_density hd, GaussianFrequency.density_eq_gaussian hd]
  exact gaussian_gain_eq_frequency _ _ _ _ _ hf hm

end BoltzmannNonuniqueness.JetBarrierCollision

end

end

section

/-! # Gaussian decay of a cold barrier away from its spatial core -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetGaussianEscape

theorem centered_gaussian_le {b : ℝ} (hb : 8 ≤ b) (u v : Velocity) :
    Real.exp (-b * ‖v - u‖ ^ 2) ≤
      Real.exp (8 * ‖u‖ ^ 2) * Real.exp (-4 * ‖v‖ ^ 2) := by
  have hn : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
    simpa only [sub_add_cancel] using norm_add_le (v - u) u
  have hs : ‖v‖ ^ 2 ≤ 2 * ‖v - u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg v, norm_nonneg (v - u), norm_nonneg u,
      sq_nonneg (‖v - u‖ - ‖u‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v - u‖)]

theorem gaussian_le_hot (q : ℝ) (v : Velocity) :
    Real.exp (-2 * ‖v‖ ^ 2) ≤ tiltConstant * H q v := by
  have hp := polynomial_le_gaussian v
  have hw : 1 ≤ W q v := by unfold W; linarith [singularity_nonneg q (transverse v)]
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-2 * ‖v‖ ^ 2))
  have hexp : Real.exp (-2 * ‖v‖ ^ 2) * Real.exp (‖v‖ ^ 2) = Real.exp (-‖v‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp (-2 * ‖v‖ ^ 2) * HotWeight.polynomial v ≤
      tiltConstant * HotWeight.G q v := by
    calc
      _ ≤ tiltConstant * Real.exp (-‖v‖ ^ 2) := by
        change Real.exp (-2 * ‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (50 : ℕ) ≤ _
        calc
          _ ≤ Real.exp (-2 * ‖v‖ ^ 2) * (tiltConstant * Real.exp (‖v‖ ^ 2)) := hm
          _ = _ := by rw [mul_left_comm, hexp]
      _ ≤ _ := by
        unfold HotWeight.G
        simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hw
          (mul_nonneg tiltConstant_pos.le (Real.exp_nonneg (-‖v‖ ^ 2)))
  rw [← HotWeight.H_mul_polynomial] at hprod
  exact (mul_le_mul_iff_of_pos_right (HotWeight.polynomial_pos v)).mp (by
    simpa only [mul_assoc] using hprod)

def constant (α : ℝ) : ℝ :=
  Real.exp 4 * JetThermalKernel.bound * Real.exp (8 * (1 + α) ^ 2)

theorem barrier_velocity_decay {K α s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16) (htmax : t ≤ 1)
    (η γ : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    barrier η K α γ s d t a (x, v) ≤
      constant α * (K / s) * (d ^ 3)⁻¹ *
        Real.exp (-(1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t)) *
          Real.exp (-4 * ‖v‖ ^ 2) := by
  have hb : 8 ≤ (2 - t) / d ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hdmax)]
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := x.2) hα
  rw [hsiga] at hu
  have hu2 : ‖centerVelocity α γ s t a x‖ ^ 2 ≤ (1 + α) ^ 2 := by
    rw [centerVelocity, PlaneChart.norm_join_sq, norm_zero, zero_pow (by norm_num), zero_add]
    nlinarith [sq_abs (AxialFlow.velocity (sign a) α γ s t x.2),
      abs_nonneg (AxialFlow.velocity (sign a) α γ s t x.2)]
  have he := (centered_gaussian_le hb (centerVelocity α γ s t a x) v).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith :
      8 * ‖centerVelocity α γ s t a x‖ ^ 2 ≤ 8 * (1 + α) ^ 2)) (Real.exp_nonneg _))
  rw [JetBarrierCollision.barrier_eq_density hd, GaussianFrequency.density_eq_gaussian hd]
  unfold gaussian
  apply (mul_le_mul_of_nonneg_left he (mul_nonneg
    (JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x) (by positivity))).trans
  unfold JetBarrierCollision.massScale constant
  have het : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr htmax
  rw [sub_eq_add_neg, Real.exp_add]
  have h4 : Real.exp 3 * Real.exp 1 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    _ = (Real.exp 3 * Real.exp t) * JetThermalKernel.bound * (K / s) * (d ^ 3)⁻¹ *
        Real.exp (-(1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t)) *
        Real.exp (8 * (1 + α) ^ 2) * Real.exp (-4 * ‖v‖ ^ 2) := by ring_nf
    _ ≤ (Real.exp 3 * Real.exp 1) * JetThermalKernel.bound * (K / s) * (d ^ 3)⁻¹ *
        Real.exp (-(1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t)) *
        Real.exp (8 * (1 + α) ^ 2) * Real.exp (-4 * ‖v‖ ^ 2) := by
      gcongr
      exact JetThermalKernel.bound_pos.le
    _ = _ := by rw [h4]; ring

end BoltzmannNonuniqueness.JetGaussianEscape

end

end

section

/-! # Almost-everywhere distance derivatives along the cold-jet flights -/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialTransport
open BoltzmannNonuniqueness.AxialFlightDerivative

namespace BoltzmannNonuniqueness.JetDistanceDerivative

theorem infDist_comp_derivative_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} {g' : E} {t : ℝ} (s : Set E) (hg : HasDerivAt g g' t)
    (hD : DifferentiableAt ℝ (fun r => infDist (g r) s) t) :
    |deriv (fun r => infDist (g r) s) t| ≤ ‖g'‖ := by
  have h := le_of_tendsto_of_tendsto hD.hasDerivAt.tendsto_slope.norm hg.tendsto_slope.norm
    (Eventually.of_forall (fun r => ?_))
  · simpa only [Real.norm_eq_abs] using h
  · dsimp only
    rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      (lipschitz_infDist_pt s).dist_le_mul (g r) (g t)

def transverseDistance (η s : ℝ) (a : Bool) (y w : Transverse) (t : ℝ) : ℝ :=
  infDist (y + t • w) (JetGeometry.mask η s a)

def axialDistance (σ α γ s z v t : ℝ) : ℝ :=
  infDist (flightFoot σ α γ s z v t) (Icc (-(1 / 8 : ℝ)) (1 / 8))

theorem transverse_lipschitz (η s : ℝ) (a : Bool) (y w : Transverse) :
    LipschitzWith ‖w‖₊ (transverseDistance η s a y w) := by
  change LipschitzWith ‖w‖₊ ((fun x => infDist x (JetGeometry.mask η s a)) ∘
    (fun t : ℝ => y + t • w))
  have hg : LipschitzWith ‖w‖₊ (fun t : ℝ => y + t • w) := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    have he : y + t • w - (y + r • w) = (t - r) • w := by module
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, Real.dist_eq]
    exact le_of_eq (mul_comm _ _)
  simpa only [one_mul] using (lipschitz_infDist_pt (JetGeometry.mask η s a)).comp hg

theorem transverse_ae_derivative_bound (η s : ℝ) (a : Bool) (y w : Transverse) :
    ∀ᵐ t, DifferentiableAt ℝ (transverseDistance η s a y w) t ∧
      |deriv (transverseDistance η s a y w) t| ≤ ‖w‖ := by
  have h := transverse_lipschitz η s a y w
  filter_upwards [h.ae_differentiableAt] with t ht
  exact ⟨ht, by simpa only [Real.norm_eq_abs, coe_nnnorm] using ht.hasDerivAt.le_of_lipschitz h⟩

theorem flightFoot_lipschitzOn {σ α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (z v : ℝ) :
    LipschitzOnWith (Real.toNNReal (|v| + |σ| + α)) (flightFoot σ α γ s z v) (Ici 0) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht r hr
  have h := flightFoot_distance (σ := σ) hα hγ hs hr z v t
  simpa only [Real.dist_eq, Real.coe_toNNReal _ (by positivity : 0 ≤ |v| + |σ| + α), mul_comm]
    using h

theorem axial_ae_differentiable {σ α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (z v : ℝ) :
    ∀ᵐ t, 0 < t → DifferentiableAt ℝ (axialDistance σ α γ s z v) t := by
  have h := (lipschitz_infDist_pt (Icc (-(1 / 8 : ℝ)) (1 / 8))).comp_lipschitzOnWith
    (flightFoot_lipschitzOn (σ := σ) hα hγ hs z v)
  filter_upwards [h.ae_differentiableWithinAt_of_mem] with t ht htpos
  exact (ht htpos.le).differentiableAt (Ici_mem_nhds htpos)

theorem axial_derivative_bound {σ α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (z v : ℝ)
    (hD : DifferentiableAt ℝ (axialDistance σ α γ s z v) t) :
    |deriv (axialDistance σ α γ s z v) t| ≤
      |(v - flightVelocity σ α γ s z v t) /
        (1 + t * AxialDerivative.A α γ s (flightFoot σ α γ s z v t))| := by
  change |deriv (fun r => infDist (flightFoot σ α γ s z v r) (Icc (-(1 / 8 : ℝ)) (1 / 8))) t| ≤ _
  simpa only [Real.norm_eq_abs] using infDist_comp_derivative_bound _
    (flightFoot_derivative hα hγ hs ht z v) hD

end BoltzmannNonuniqueness.JetDistanceDerivative

end

end

section

/-! # Local mass bounds for the Gaussian cold barrier, uniform in thermal width -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetBarrierLocalMass

def massConstant : ℝ := Real.exp 4*JetThermalKernel.bound*JetGaussianMoments.mass

theorem massConstant_nonneg : 0 ≤ massConstant := by
  unfold massConstant
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le JetThermalKernel.bound_pos.le)
    JetGaussianMoments.mass_nonneg

theorem measurable_barrier {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K d : ℝ) (a : Bool) :
    Measurable (barrier η K α γ s d t a) := by
  have hv : Measurable (fun p : JetPrototype.Phase => AxialFlow.velocity (sign a) α γ s t p.1.2) :=
    (AxialFlow.continuous_velocity hα hγ hs ht).measurable.comp measurable_fst.snd
  have hc : Measurable (fun p : JetPrototype.Phase => centerVelocity α γ s t a p.1) :=
    SheetMeasures.join.measurable.comp (measurable_const.prodMk hv)
  have hf : Measurable (fun p : JetPrototype.Phase => AxialFlow.foot (sign a) α γ s t p.1.2) :=
    (AxialFlow.foot_lipschitzWith hα hγ hs ht).continuous.measurable.comp measurable_fst.snd
  have hx : Measurable (fun p : JetPrototype.Phase => distanceSquared η α γ s t a p.1) :=
    ((((continuous_infDist_pt (s := JetGeometry.mask η s a)).measurable.comp measurable_fst.fst).pow_const 2).add
      (((continuous_infDist_pt (s := Icc (-(1/8:ℝ)) (1/8))).measurable.comp hf).pow_const 2))
  unfold barrier exponent
  exact measurable_const.mul ((measurable_const.sub
    (measurable_const.mul ((measurable_snd.sub hc).norm.pow_const 2) |>.div_const _)).sub
    (measurable_const.mul hx |>.div_const _)).exp

theorem velocity_integrable {d t : ℝ} (hd : 0 < d) (htmax : t ≤ 1)
    (η K α γ s : ℝ) (a : Bool) (x : Space) :
    Integrable (fun v => barrier η K α γ s d t a (x,v)) := by
  simp_rw [JetBarrierCollision.barrier_eq_density hd]
  exact GaussianFrequency.integrable (by linarith) hd _ _

theorem velocity_integral_le {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) :
    (∫ v, barrier η K α γ s d t a (x,v)) ≤ massConstant*(K/s) := by
  simp_rw [JetBarrierCollision.barrier_eq_density hd]
  apply (GaussianFrequency.mass_le (JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x)
    (by linarith) hd _).trans
  have h := mul_le_mul_of_nonneg_right
    (JetBarrierCollision.massScale_le hK hs hd ht htmax η α γ a x) JetGaussianMoments.mass_nonneg
  convert h using 1
  unfold massConstant
  ring

theorem local_integrable {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (η : ℝ) (a : Bool) (y : Space) (μ : Measure Space) [IsFiniteMeasure μ] :
    Integrable (fun p : JetPrototype.Phase => barrier η K α γ s d t a (p.1-y,p.2)) (μ.prod volume) := by
  have hm : Measurable (fun p : JetPrototype.Phase => barrier η K α γ s d t a (p.1-y,p.2)) :=
    (measurable_barrier hα hγ hs ht.le η K d a).comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => velocity_integrable hd htmax η K α γ s a (x-y)),?_⟩
  apply Integrable.of_bound (hm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    (massConstant*(K/s))
  filter_upwards [] with x
  simp_rw [Real.norm_of_nonneg (barrier_nonneg hK hs.le hd.le η α γ t a _)]
  rw [Real.norm_of_nonneg (integral_nonneg (fun v => barrier_nonneg hK hs.le hd.le η α γ t a _))]
  exact velocity_integral_le hK hs hd ht htmax η α γ a (x-y)

theorem local_integral_le {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (η : ℝ) (a : Bool) (y : Space) (μ : Measure Space) [IsFiniteMeasure μ] :
    (∫ p : JetPrototype.Phase, barrier η K α γ s d t a (p.1-y,p.2) ∂μ.prod volume) ≤
      μ.real univ*(massConstant*(K/s)) := by
  have hi := local_integrable hK hα hγ hs hd ht htmax η a y μ
  rw [integral_prod _ hi]
  have h := integral_mono_ae hi.integral_prod_left (integrable_const (massConstant*(K/s)))
    (ae_of_all _ (fun x => velocity_integral_le hK hs hd ht htmax η α γ a (x-y)))
  simpa only [integral_const,smul_eq_mul] using h

end BoltzmannNonuniqueness.JetBarrierLocalMass

end

end

section

/-! # Positive spatial distance for every nonmain cold label -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetEscapeGeometry

theorem transverse_distance {η s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (a : Bool) {y : Transverse} (hy : y ∉ enlargement η s a) :
    enlargementWidth η s ≤ infDist y (mask η s a) := by
  apply le_of_not_gt
  intro hd
  apply hy
  exact thickening_subset_cthickening (enlargementWidth η s) (mask η s a)
    ((mem_thickening_iff_infDist_lt
    (JetMaskNonempty.mask_nonempty hη hs hsmax a)).mpr hd)

theorem axial_distance {α t : ℝ} (hα : 0 ≤ α) (hαmax : α ≤ 1) (ht : 0 ≤ t)
    (γ s z : ℝ) (a : Bool) (hz : 1 / 8 + 2 * t + 1 / 16 < |z|) :
    (1 / 16 : ℝ) ≤ infDist (AxialFlow.foot (sign a) α γ s t z) (Icc (-(1 / 8 : ℝ)) (1 / 8)) := by
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := z) hα
  rw [hsiga] at hu
  have hu' : t * |AxialFlow.velocity (sign a) α γ s t z| ≤ 2 * t := by
    nlinarith [mul_le_mul_of_nonneg_left hu ht, mul_le_mul_of_nonneg_left hαmax ht]
  have htri : |z| ≤ |AxialFlow.foot (sign a) α γ s t z| + t * |AxialFlow.velocity (sign a) α γ s t z| := by
    have h := abs_add_le (AxialFlow.foot (sign a) α γ s t z)
      (t * AxialFlow.velocity (sign a) α γ s t z)
    simp only [AxialFlow.foot, sub_add_cancel, abs_mul, abs_of_nonneg ht] at h
    exact h
  apply (le_infDist (show (Icc (-(1 / 8 : ℝ)) (1 / 8)).Nonempty from ⟨0, by norm_num⟩)).mpr
  intro r hr
  have hrabs : |r| ≤ (1 / 8 : ℝ) := abs_le.mpr hr
  have htri' := abs_add_le (AxialFlow.foot (sign a) α γ s t z - r) r
  rw [sub_add_cancel] at htri'
  rw [Real.dist_eq]
  linarith

theorem width_le {η s : ℝ} (hηmax : η ≤ Real.log 2)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) : enlargementWidth η s ≤ 1 / 16 := by
  have hc := gapCoefficient_le hηmax
  have hs2 : s ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hs.le hsmax 2
  unfold enlargementWidth
  calc
    _ ≤ ((1 / 16 : ℝ) / 4) * (1 / 8) ^ 2 :=
      mul_le_mul (div_le_div_of_nonneg_right hc (by norm_num)) hs2 (sq_nonneg s) (by norm_num)
    _ ≤ _ := by norm_num

theorem distance_lower_bound {η α s t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8) (ht : 0 ≤ t)
    (γ : ℝ) (a : Bool) (x : Space)
    (hout : ¬(x.1 ∈ enlargement η s a ∧ |x.2| ≤ 1 / 8 + 2 * t + 1 / 16)) :
    (enlargementWidth η s) ^ 2 ≤ distanceSquared η α γ s t a x := by
  have hδ := (enlargementWidth_pos hη hs).le
  by_cases hy : x.1 ∈ enlargement η s a
  · have hz : 1 / 8 + 2 * t + 1 / 16 < |x.2| := lt_of_not_ge (fun hz => hout ⟨hy, hz⟩)
    have hd := (width_le hηmax hs hsmax).trans (axial_distance hα hαmax ht γ s x.2 a hz)
    unfold distanceSquared
    have hsq := (sq_le_sq₀ hδ (show 0 ≤ infDist (AxialFlow.foot (sign a) α γ s t x.2)
      (Icc (-(1 / 8 : ℝ)) (1 / 8)) from infDist_nonneg)).mpr hd
    nlinarith only [hsq, sq_nonneg (infDist x.1 (mask η s a))]
  · have hd := transverse_distance hη hs hsmax a hy
    unfold distanceSquared
    have hsq := (sq_le_sq₀ hδ (show 0 ≤ infDist x.1 (mask η s a) from infDist_nonneg)).mpr hd
    nlinarith only [hsq, sq_nonneg (infDist (AxialFlow.foot (sign a) α γ s t x.2)
      (Icc (-(1 / 8 : ℝ)) (1 / 8)))]

end BoltzmannNonuniqueness.JetEscapeGeometry

end

end

section

/-! # Arbitrary polynomial decay of the escaped-scale exponential -/

noncomputable section

namespace BoltzmannNonuniqueness.JetEscapePower

theorem exp_neg_le {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.exp (-x) ≤ (m.factorial : ℝ) / x ^ m := by
  have hfact : 0 < (m.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp x hx.le m)
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos hx m)).mpr
  calc
    _ ≤ (Real.exp x)⁻¹ * (Real.exp x * (m.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero x), one_mul]

def tail (β s t : ℝ) : ℝ := (s ^ 31)⁻¹ * Real.exp (-β / (s ^ 16 * t))

theorem tail_nonneg {s : ℝ} (hs : 0 ≤ s) (β t : ℝ) : 0 ≤ tail β s t := by
  unfold tail
  positivity

theorem tail_bound {β s t : ℝ} (hβ : 0 < β) (hs : 0 < s) (ht : 0 < t)
    (m : ℕ) (hm : 31 ≤ 16 * m) :
    tail β s t ≤ ((m.factorial : ℝ) / β ^ m) * t ^ m * s ^ (16 * m - 31) := by
  have hx : 0 < β / (s ^ 16 * t) := by positivity
  have h := mul_le_mul_of_nonneg_left (exp_neg_le hx m) (by positivity : 0 ≤ (s ^ 31)⁻¹)
  rw [← neg_div] at h
  change tail β s t ≤ _ at h
  apply h.trans_eq
  rw [div_pow, mul_pow]
  have hpow : s ^ (16 * m) = s ^ (16 * m - 31) * s ^ 31 := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  rw [← pow_mul, hpow]
  field_simp


theorem summable_tails {β s₀ η t : ℝ} (hβ : 0 < β) (hs₀ : 0 < s₀)
    (hη : 0 < η) (ht : 0 < t) :
    Summable (fun j : ℕ => tail β (DatumBounds.scale s₀ η j) t) := by
  have hm := (DatumBounds.summable_scale_pow s₀ hη 1 (by norm_num)).mul_left
    (((2 : ℕ).factorial : ℝ) / β ^ 2 * t ^ 2)
  apply Summable.of_nonneg_of_le
    (fun j => tail_nonneg (DatumBounds.scale_pos (η := η) hs₀ j).le β t) _ hm
  intro j
  simpa only [Nat.factorial_two, Nat.cast_ofNat, Nat.reduceMul, Nat.reduceSub, pow_one] using
    tail_bound hβ (DatumBounds.scale_pos (η := η) hs₀ j) ht 2 (by norm_num)

theorem sum_bound {β s₀ η t : ℝ} (hβ : 0 < β) (hs₀ : 0 < s₀)
    (hη : 0 < η) (ht : 0 < t) (m : ℕ) (hm : 31 < 16 * m) :
    (∑' j : ℕ, tail β (DatumBounds.scale s₀ η j) t) ≤
      ((m.factorial : ℝ) / β ^ m * t ^ m) *
        ∑' j : ℕ, DatumBounds.scale s₀ η j ^ (16 * m - 31) := by
  have hp : 0 < 16 * m - 31 := Nat.sub_pos_of_lt hm
  have hs := (DatumBounds.summable_scale_pow s₀ hη (16 * m - 31) hp).mul_left
    ((m.factorial : ℝ) / β ^ m * t ^ m)
  rw [← tsum_mul_left]
  exact (summable_tails hβ hs₀ hη ht).tsum_le_tsum
    (fun j => tail_bound hβ (DatumBounds.scale_pos (η := η) hs₀ j) ht m hm.le) hs

end BoltzmannNonuniqueness.JetEscapePower

end

end

section

/-! # The escaped barrier has the actual s⁻³¹ exp(-β/(s¹⁶t)) tail -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetEscapedBarrier

def rate (η d₀ : ℝ) : ℝ := (gapCoefficient η / 4) ^ 2 / (8 * d₀ ^ 2)

def coefficient (α K d₀ : ℝ) : ℝ := JetGaussianEscape.constant α * K * (d₀ ^ 3)⁻¹

theorem rate_pos {η d₀ : ℝ} (hη : 0 < η) (hd₀ : 0 < d₀) : 0 < rate η d₀ := by
  have := gapCoefficient_pos hη
  unfold rate
  positivity

theorem spatial_exponent {η α s d₀ t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (hd₀ : 0 < d₀) (ht : 0 < t) (γ : ℝ) (a : Bool) (x : Space)
    (hout : ¬(x.1 ∈ enlargement η s a ∧ |x.2| ≤ 1 / 8 + 2 * t + 1 / 16)) :
    rate η d₀ / (s ^ 16 * t) ≤
      (1 / 8 : ℝ) * distanceSquared η α γ s t a x / ((d₀ * s ^ 10) ^ 2 * t) := by
  have hD := JetEscapeGeometry.distance_lower_bound hη hηmax hα hαmax hs hsmax ht.le γ a x hout
  have he : rate η d₀ / (s ^ 16 * t) =
      (1 / 8 : ℝ) * (enlargementWidth η s) ^ 2 / ((d₀ * s ^ 10) ^ 2 * t) := by
    unfold rate enlargementWidth
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num)) (by positivity)

theorem barrier_bound {η K α s d₀ t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (hd₀ : 0 < d₀) (hwidth : d₀ * s ^ 10 ≤ 1 / 16) (ht : 0 < t) (htmax : t ≤ 1)
    (γ : ℝ) (a : Bool) (x : Space) (v : Velocity)
    (hout : ¬(x.1 ∈ enlargement η s a ∧ |x.2| ≤ 1 / 8 + 2 * t + 1 / 16)) :
    barrier η K α γ s (d₀ * s ^ 10) t a (x, v) ≤
      coefficient α K d₀ * JetEscapePower.tail (rate η d₀) s t * Real.exp (-4 * ‖v‖ ^ 2) := by
  have hd : 0 < d₀ * s ^ 10 := by positivity
  have hb := JetGaussianEscape.barrier_velocity_decay hK hα hs hd hwidth htmax η γ a x v
  have hD := spatial_exponent hη hηmax hα hαmax hs hsmax hd₀ ht γ a x hout
  have he : Real.exp (-(1 / 8 : ℝ) * distanceSquared η α γ s t a x / ((d₀ * s ^ 10) ^ 2 * t)) ≤
      Real.exp (-rate η d₀ / (s ^ 16 * t)) := by
    apply Real.exp_le_exp.mpr
    convert neg_le_neg hD using 1 <;> ring
  have hC : 0 ≤ JetGaussianEscape.constant α * (K / s) * ((d₀ * s ^ 10) ^ 3)⁻¹ := by
    unfold JetGaussianEscape.constant
    have := JetThermalKernel.bound_pos
    positivity
  calc
    _ ≤ JetGaussianEscape.constant α * (K / s) * ((d₀ * s ^ 10) ^ 3)⁻¹ *
        Real.exp (-rate η d₀ / (s ^ 16 * t)) * Real.exp (-4 * ‖v‖ ^ 2) :=
      hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hC) (Real.exp_nonneg _))
    _ = _ := by unfold coefficient JetEscapePower.tail; field_simp

end BoltzmannNonuniqueness.JetEscapedBarrier

end

end

end OAI
