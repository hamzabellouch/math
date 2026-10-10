import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarrierKinetic
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusChart

namespace OAI

section

/-! # Integration of spatial weights against the cold thermal kernel -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalLaw

namespace BoltzmannNonuniqueness.JetWeightedKernel

def weighted (d α γ s : ℝ) (a : Bool) (w : Space → ℝ) (f : Velocity → ℝ)
    (p : JetPrototype.Phase) : ℝ := w p.1 * scaled d (center α γ s a p.1.2) f p.2

theorem weighted_nonneg {d : ℝ} (hd : 0 ≤ d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : ∀ x, 0 ≤ w x) {f : Velocity → ℝ} (hf : ∀ v, 0 ≤ f v)
    (p : JetPrototype.Phase) : 0 ≤ weighted d α γ s a w f p := by
  exact mul_nonneg (hw _) (mul_nonneg (inv_nonneg.mpr (pow_nonneg hd 3)) (hf _))

theorem weighted_measurable (d α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) {f : Velocity → ℝ} (hf : Measurable f) :
    Measurable (weighted d α γ s a w f) := by
  have hc : Measurable (fun p : JetPrototype.Phase => center α γ s a p.1.2) :=
    (measurable_center α γ s a).comp (measurable_snd.comp measurable_fst)
  have harg : Measurable (fun p : JetPrototype.Phase => d⁻¹ • (p.2 - center α γ s a p.1.2)) :=
    (measurable_const : Measurable (fun _ : JetPrototype.Phase => d⁻¹)).smul (measurable_snd.sub hc)
  exact (hw.comp measurable_fst).mul (measurable_const.mul (hf.comp harg))

theorem weighted_velocity_integral {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    (w : Space → ℝ) (f : Velocity → ℝ) (x : Space) :
    (∫ v, weighted d α γ s a w f (x, v)) = w x * ∫ v, f v := by
  change (∫ v, w x * scaled d (center α γ s a x.2) f v) = _
  rw [integral_const_mul, integral_scaled f hd]

theorem weighted_integrable {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) (hwi : Integrable w spaceVolume) (hwp : ∀ x, 0 ≤ w x)
    {f : Velocity → ℝ} (hf : Measurable f) (hfi : Integrable f) (hfp : ∀ v, 0 ≤ f v) :
    Integrable (weighted d α γ s a w f) (spaceVolume.prod volume) := by
  apply (integrable_prod_iff (weighted_measurable d α γ s a hw hf).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    exact (integrable_scaled hfi hd (center α γ s a x.2)).const_mul (w x)
  · have he : (fun x : Space => ∫ v, ‖weighted d α γ s a w f (x, v)‖) =
        fun x => w x * ∫ v, f v := by
      funext x
      simp_rw [Real.norm_of_nonneg (weighted_nonneg hd.le α γ s a hwp hfp _)]
      exact weighted_velocity_integral hd α γ s a w f x
    rw [he]
    exact hwi.mul_const _

theorem weighted_integral {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) (hwi : Integrable w spaceVolume) (hwp : ∀ x, 0 ≤ w x)
    {f : Velocity → ℝ} (hf : Measurable f) (hfi : Integrable f) (hfp : ∀ v, 0 ≤ f v) :
    (∫ p, weighted d α γ s a w f p ∂spaceVolume.prod volume) =
      (∫ x, w x ∂spaceVolume) * ∫ v, f v := by
  rw [integral_prod _ (weighted_integrable hd α γ s a hw hwi hwp hf hfi hfp)]
  simp_rw [weighted_velocity_integral hd α γ s a]
  exact integral_mul_const _ _

end BoltzmannNonuniqueness.JetWeightedKernel

end

end

section

/-! # Absolute entropy of each actual cold-jet prototype -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalKernel
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetWeightedKernel

namespace BoltzmannNonuniqueness.JetPrototypeEntropy

theorem measurable_entropy {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) : Measurable (fun x => entropy (f x)) :=
  hf.mul (Real.measurable_log.comp hf).abs

def spatialWeight (η K γ s d : ℝ) (a : Bool) (x : Space) : ℝ :=
  entropy (spatial η K γ s a x) + (3 * |Real.log d|) * spatial η K γ s a x

def majorant (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  weighted d α γ s a (spatialWeight η K γ s d a) J p +
    weighted d α γ s a (spatial η K γ s a) (fun v => entropy (J v)) p

theorem spatialWeight_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s)
    (η γ d : ℝ) (a : Bool) (x : Space) : 0 ≤ spatialWeight η K γ s d a x :=
  add_nonneg (entropy_nonneg (spatial_nonneg hK hs η γ a x))
    (mul_nonneg (by positivity) (spatial_nonneg hK hs η γ a x))

theorem spatialWeight_measurable (η K γ s d : ℝ) (a : Bool) :
    Measurable (spatialWeight η K γ s d a) :=
  (measurable_entropy (measurable_spatial η K γ s a)).add
    (measurable_const.mul (measurable_spatial η K γ s a))

theorem spatialWeight_integrable {η K γ s : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (d : ℝ) (a : Bool) :
    Integrable (spatialWeight η K γ s d a) spaceVolume :=
  (JetSpatialEntropy.spatial_entropy_integrable hη hK hγ hs a).add
    ((spatial_integrable hη K γ s a).const_mul _)

theorem entropy_le_majorant {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hd : 0 < d) (η α γ : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    entropy (density η K α γ s d a p) ≤ majorant η K α γ s d a p := by
  have hw := spatial_nonneg hK hs η γ a p.1
  have h₁ := entropy_mul_le hw
    (JetThermalLaw.density_nonneg hd.le (center α γ s a p.1.2) p.2)
  have h₂ := mul_le_mul_of_nonneg_left
    (density_entropy_bound hd (center α γ s a p.1.2) p.2) hw
  unfold density at *
  unfold JetThermalLaw.density at h₁ h₂
  unfold majorant weighted spatialWeight JetThermalLaw.density
  nlinarith only [h₁, h₂]

theorem majorant_integrable {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    Integrable (majorant η K α γ s d a) (spaceVolume.prod volume) := by
  apply Integrable.add
  · exact weighted_integrable hd α γ s a (spatialWeight_measurable η K γ s d a)
      (spatialWeight_integrable hη hK hγ hs d a)
      (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable
      J_integrable J_nonneg
  · exact weighted_integrable hd α γ s a (measurable_spatial η K γ s a)
      (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
      (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
      (fun v => entropy_nonneg (J_nonneg v))

theorem density_entropy_integrable {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    Integrable (fun p => entropy (density η K α γ s d a p))
      (spaceVolume.prod volume) := by
  apply (majorant_integrable hη hK hγ hs hd α a).mono'
  · exact (measurable_entropy (measurable_density η K α γ s d a)).aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_of_nonneg (entropy_nonneg (density_nonneg hK hs.le hd.le η α γ a p))]
    exact entropy_le_majorant hK hs.le hd η α γ a p

theorem density_entropy_integral {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    (∫ p, entropy (density η K α γ s d a p) ∂spaceVolume.prod volume) ≤
      (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) +
        (3 * |Real.log d| + JetThermalEntropy.entropyConstant) *
          ∫ x, spatial η K γ s a x ∂spaceVolume := by
  apply (integral_mono (density_entropy_integrable hη hK hγ hs hd α a)
    (majorant_integrable hη hK hγ hs hd α a)
    (entropy_le_majorant hK hs.le hd η α γ a)).trans_eq
  have hi₁ := weighted_integrable hd α γ s a (spatialWeight_measurable η K γ s d a)
    (spatialWeight_integrable hη hK hγ hs d a)
    (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable
    J_integrable J_nonneg
  have hi₂ := weighted_integrable hd α γ s a (measurable_spatial η K γ s a)
    (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
    (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
    (fun v => entropy_nonneg (J_nonneg v))
  unfold majorant
  rw [integral_add hi₁ hi₂,
    weighted_integral hd α γ s a (spatialWeight_measurable η K γ s d a)
      (spatialWeight_integrable hη hK hγ hs d a)
      (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable J_integrable J_nonneg,
    weighted_integral hd α γ s a (measurable_spatial η K γ s a)
      (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
      (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
      (fun v => entropy_nonneg (J_nonneg v)), J_integral, mul_one]
  unfold spatialWeight JetThermalEntropy.entropyConstant
  rw [integral_add (JetSpatialEntropy.spatial_entropy_integrable hη hK hγ hs a)
    ((spatial_integrable hη K γ s a).const_mul _), integral_const_mul]
  ring

end BoltzmannNonuniqueness.JetPrototypeEntropy

end

end

section

/-! # The scale-uniform, summable cold-jet entropy bound -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure

namespace BoltzmannNonuniqueness.JetEntropyBound

def spatialConstant (K γ : ℝ) : ℝ :=
  4 * Real.pi * (K / γ) * ((|Real.log K| + 1) * JetSpatialEntropy.massConstant +
    JetSpatialEntropy.entropyConstant)

def constant (K γ d₀ : ℝ) : ℝ := spatialConstant K γ +
  (3 * (|Real.log d₀| + 10) + JetThermalEntropy.entropyConstant) * (8 * Real.pi * K / γ)

theorem spatialConstant_nonneg {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) :
    0 ≤ spatialConstant K γ := by
  have := JetSpatialEntropy.massConstant_nonneg
  have := JetSpatialEntropy.entropyConstant_nonneg
  unfold spatialConstant
  positivity

theorem constant_nonneg {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) (d₀ : ℝ) :
    0 ≤ constant K γ d₀ := by
  have := spatialConstant_nonneg hK hγ
  have := JetThermalEntropy.entropyConstant_nonneg
  unfold constant
  positivity

theorem spatial_mass_bound {η K γ s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x, spatial η K γ s a x ∂spaceVolume) ≤ (8 * Real.pi * K / γ) * s ^ 2 := by
  have h := density_mass_bound hη hηmax hK hγ hs (show (0 : ℝ) < 1 by norm_num) 0 a
  rw [integral_prod _ (density_integrable hη hK hs.le (show (0 : ℝ) < 1 by norm_num) 0 γ a)] at h
  simpa only [density_velocity_integral (show (0 : ℝ) < 1 by norm_num)] using h

theorem spatial_entropy_bound {η K γ s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) ≤
      spatialConstant K γ * s ^ 2 * (1 + |Real.log s|) := by
  have hM := JetSpatialEntropy.massConstant_nonneg
  have hE := JetSpatialEntropy.entropyConstant_nonneg
  have hlog : |Real.log (K / s)| ≤ |Real.log K| + |Real.log s| := by
    rw [Real.log_div hK.ne' hs.ne']
    exact abs_sub _ _
  have heq : (s / γ) * (entropy (K / s) * JetSpatialEntropy.massConstant +
      (K / s) * JetSpatialEntropy.entropyConstant) =
      (K / γ) * (|Real.log (K / s)| * JetSpatialEntropy.massConstant +
        JetSpatialEntropy.entropyConstant) := by
    unfold entropy
    field_simp
  have hscalar : (|Real.log K| + |Real.log s|) * JetSpatialEntropy.massConstant +
      JetSpatialEntropy.entropyConstant ≤
      ((|Real.log K| + 1) * JetSpatialEntropy.massConstant + JetSpatialEntropy.entropyConstant) *
        (1 + |Real.log s|) := by
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (Real.log K)) hM) (abs_nonneg (Real.log s)),
      mul_nonneg hE (abs_nonneg (Real.log s))]
  calc
    _ ≤ volume.real (mask η s a) * ((s / γ) *
        (entropy (K / s) * JetSpatialEntropy.massConstant +
          (K / s) * JetSpatialEntropy.entropyConstant)) := by
      simpa only [mul_assoc] using JetSpatialEntropy.spatial_entropy_integral hK.le hγ hs a
    _ = volume.real (mask η s a) * (K / γ) *
        (|Real.log (K / s)| * JetSpatialEntropy.massConstant + JetSpatialEntropy.entropyConstant) := by
      rw [heq, mul_assoc]
    _ ≤ (4 * Real.pi * s ^ 2) * (K / γ) *
        ((|Real.log K| + |Real.log s|) * JetSpatialEntropy.massConstant +
          JetSpatialEntropy.entropyConstant) := by
      gcongr
      exact mask_area_uniform hη hηmax hs.le a
    _ ≤ (4 * Real.pi * s ^ 2) * (K / γ) *
        (((|Real.log K| + 1) * JetSpatialEntropy.massConstant +
          JetSpatialEntropy.entropyConstant) * (1 + |Real.log s|)) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by unfold spatialConstant; ring

theorem thermal_log_bound {d₀ s : ℝ} (hd₀ : 0 < d₀) (hs : 0 < s) :
    3 * |Real.log (d₀ * s ^ 10)| + JetThermalEntropy.entropyConstant ≤
      (3 * (|Real.log d₀| + 10) + JetThermalEntropy.entropyConstant) * (1 + |Real.log s|) := by
  have hlog : |Real.log (d₀ * s ^ 10)| ≤ |Real.log d₀| + 10 * |Real.log s| := by
    rw [Real.log_mul hd₀.ne' (pow_ne_zero _ hs.ne'), Real.log_pow]
    have h := abs_add_le (Real.log d₀) (10 * Real.log s)
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10), Nat.cast_ofNat] using h
  have hE := JetThermalEntropy.entropyConstant_nonneg
  nlinarith [mul_nonneg (abs_nonneg (Real.log d₀)) (abs_nonneg (Real.log s)),
    mul_nonneg hE (abs_nonneg (Real.log s))]

/-- The constant depends only on the fixed parameters, and is independent of the annular scale. -/
theorem prototype_entropy_bound {η K γ s d₀ : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hs : 0 < s) (hd₀ : 0 < d₀) (α : ℝ) (a : Bool) :
    (∫ p, entropy (density η K α γ s (d₀ * s ^ 10) a p) ∂spaceVolume.prod volume) ≤
      constant K γ d₀ * s ^ 2 * (1 + |Real.log s|) := by
  have hd : 0 < d₀ * s ^ 10 := mul_pos hd₀ (pow_pos hs _)
  have hsp := spatial_entropy_bound hη hηmax hK hγ hs a
  have hm := spatial_mass_bound hη hηmax hK.le hγ hs a
  have ht := thermal_log_bound hd₀ hs
  have hm0 : 0 ≤ ∫ x, spatial η K γ s a x ∂spaceVolume :=
    integral_nonneg (spatial_nonneg hK.le hs.le η γ a)
  calc
    _ ≤ (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) +
        (3 * |Real.log (d₀ * s ^ 10)| + JetThermalEntropy.entropyConstant) *
          ∫ x, spatial η K γ s a x ∂spaceVolume :=
      JetPrototypeEntropy.density_entropy_integral hη hK.le hγ hs hd α a
    _ ≤ spatialConstant K γ * s ^ 2 * (1 + |Real.log s|) +
        ((3 * (|Real.log d₀| + 10) + JetThermalEntropy.entropyConstant) * (1 + |Real.log s|)) *
          ((8 * Real.pi * K / γ) * s ^ 2) := by
      exact add_le_add hsp (mul_le_mul ht hm hm0 (by
        have := JetThermalEntropy.entropyConstant_nonneg
        positivity))
    _ = _ := by unfold constant; ring

end BoltzmannNonuniqueness.JetEntropyBound

end

end

section

/-! # A coordinate box lower bound for periodic barrier distances -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetSpatialBox

theorem mask_norm_le_one {η s : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) {y : Transverse} (hy : y ∈ mask η s a) :
    ‖y‖ ≤ 1 := by
  have hn := hy.1.2
  have hc := (gapCoefficient_pos hη).le
  have he : Real.exp η ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hηmax
  have he' := mul_le_mul_of_nonneg_right he hs.le
  nlinarith [sq_nonneg s, mul_nonneg hc (sq_nonneg s)]

theorem transverse_component {η s : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) (x : Transverse) (k : Fin 2) :
    max (|x k| - 1) 0 ≤ infDist x (mask η s a) := by
  apply (le_infDist (JetMaskNonempty.mask_nonempty hη hs hsmax a)).mpr
  intro y hy
  have hyc : |y k| ≤ 1 := by
    have h := PiLp.norm_apply_le y k
    rw [Real.norm_eq_abs] at h
    exact h.trans (mask_norm_le_one hη hηmax hs hsmax a hy)
  have hdc : |x k - y k| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) k
  have htri := abs_add_le (x k - y k) (y k)
  rw [sub_add_cancel] at htri
  rw [dist_eq_norm]
  exact max_le (by linarith) (norm_nonneg _)

theorem axial_component {α t : ℝ} (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (γ s z : ℝ) (a : Bool) :
    max (|z| - 1) 0 ≤ infDist (AxialFlow.foot (sign a) α γ s t z)
      (Icc (-(1 / 8 : ℝ)) (1 / 8)) := by
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := z) hα
  rw [hsiga] at hu
  have hu' : t * |AxialFlow.velocity (sign a) α γ s t z| ≤ 2 * t := by
    nlinarith [mul_le_mul_of_nonneg_left hu ht, mul_le_mul_of_nonneg_left hαmax ht]
  have htri := abs_add_le (AxialFlow.foot (sign a) α γ s t z)
    (t * AxialFlow.velocity (sign a) α γ s t z)
  simp only [AxialFlow.foot, sub_add_cancel, abs_mul, abs_of_nonneg ht] at htri
  change |z| ≤ |AxialFlow.foot (sign a) α γ s t z| + t * |AxialFlow.velocity (sign a) α γ s t z| at htri
  apply (le_infDist (show (Icc (-(1 / 8 : ℝ)) (1 / 8)).Nonempty from ⟨0, by norm_num⟩)).mpr
  intro r hr
  have hrabs : |r| ≤ (1 / 8 : ℝ) := abs_le.mpr hr
  have htri' := abs_add_le (AxialFlow.foot (sign a) α γ s t z - r) r
  rw [sub_add_cancel] at htri'
  rw [Real.dist_eq]
  exact max_le (by linarith) (abs_nonneg _)

def shifted (x : Velocity) (n : Lattice) : Space :=
  (transverse x - transverseShift n, axial x - axialShift n)

def gap (x : Velocity) (n : Lattice) (k : Fin 3) : ℝ := max (|x k - (n k : ℝ)| - 1) 0

theorem coordinate_bound {η α s t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (γ : ℝ) (a : Bool) (x : Velocity) (n : Lattice) :
    (∑ k : Fin 3, (gap x n k) ^ 2) ≤ 2 * distanceSquared η α γ s t a (shifted x n) := by
  have h0 := transverse_component hη hηmax hs hsmax a (shifted x n).1 0
  have h1 := transverse_component hη hηmax hs hsmax a (shifted x n).1 1
  have h2 := axial_component hα hαmax ht htmax γ s (shifted x n).2 a
  change gap x n 0 ≤ infDist (shifted x n).1 (mask η s a) at h0
  change gap x n 1 ≤ infDist (shifted x n).1 (mask η s a) at h1
  change gap x n 2 ≤ infDist (AxialFlow.foot (sign a) α γ s t (shifted x n).2)
    (Icc (-(1 / 8 : ℝ)) (1 / 8)) at h2
  have h0sq := (sq_le_sq₀ (le_max_right _ _) (show 0 ≤ infDist (shifted x n).1 (mask η s a)
    from infDist_nonneg)).mpr h0
  have h1sq := (sq_le_sq₀ (le_max_right _ _) (show 0 ≤ infDist (shifted x n).1 (mask η s a)
    from infDist_nonneg)).mpr h1
  have h2sq := (sq_le_sq₀ (le_max_right _ _) (show 0 ≤ infDist (AxialFlow.foot (sign a) α γ s t (shifted x n).2)
    (Icc (-(1 / 8 : ℝ)) (1 / 8)) from infDist_nonneg)).mpr h2
  rw [Fin.sum_univ_three]
  unfold distanceSquared gap
  nlinarith only [h0sq, h1sq, h2sq, sq_nonneg (infDist (AxialFlow.foot (sign a) α γ s t (shifted x n).2)
    (Icc (-(1 / 8 : ℝ)) (1 / 8)))]

end BoltzmannNonuniqueness.JetSpatialBox

end

end

section

/-! # Integration of the nonnegative, disjoint cold-jet series -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetSeries

theorem summable_single_support {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) : Summable f := by
  classical
  by_cases h : ∃ i, f i ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact summable_of_ne_finset_zero (s := {i}) (fun j hj => hf i j (by simpa [eq_comm] using hj) hi)
  · have he : f = 0 := by ext i; simpa using not_exists.mp h i
    rw [he]
    exact summable_zero

theorem entropy_tsum {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) :
    entropy (∑' i, f i) = ∑' i, entropy (f i) := by
  classical
  by_cases h : ∃ i, f i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hz : ∀ j, j ≠ i → f j = 0 := fun j hj => hf i j hj.symm hi
    rw [tsum_eq_single i hz, tsum_eq_single i]
    intro j hj
    simp [hz j hj, entropy]
  · have hz : ∀ i, f i = 0 := fun i => not_ne_iff.mp (not_exists.mp h i)
    simp [hz, entropy]

theorem integrable_nonnegative_series {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℝ}
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (f i) μ)
    (hn : ∀ i x, 0 ≤ f i x) (hs : ∀ x, Summable (fun i => f i x))
    (hI : Summable (fun i => ∫ x, f i x ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => tsum_nonneg (fun i => hn i x)))).mpr
  have he : (∫⁻ x, ENNReal.ofReal (∑' i, f i x) ∂μ) =
      ∑' i, ENNReal.ofReal (∫ x, f i x ∂μ) := by
    simp_rw [ENNReal.ofReal_tsum_of_nonneg (fun i => hn i _) (hs _)]
    rw [lintegral_tsum (fun i => (hm i).ennreal_ofReal.aemeasurable)]
    congr 1
    funext i
    exact (ofReal_integral_eq_lintegral_ofReal (hi i)
      (Filter.Eventually.of_forall (hn i))).symm
  rw [he]
  exact hI.tsum_ofReal_lt_top

theorem integral_nonnegative_series {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℝ} (hi : ∀ i, Integrable (f i) μ)
    (hn : ∀ i x, 0 ≤ f i x) (hI : Summable (fun i => ∫ x, f i x ∂μ)) :
    (∫ x, ∑' i, f i x ∂μ) = ∑' i, ∫ x, f i x ∂μ := by
  apply (integral_tsum_of_summable_integral_norm hi _).symm
  simpa only [Real.norm_of_nonneg (hn _ _)] using hI

end BoltzmannNonuniqueness.JetSeries

end

end

section

/-! # The full unperiodized cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetDatum

abbrev Index := ℕ × Bool

def term (s₀ η K α γ d₀ : ℝ) (i : Index) : JetPrototype.Phase → ℝ :=
  density η K α γ (jetScale s₀ η i.1) (d₀ * jetScale s₀ η i.1 ^ 10) i.2

def datum (s₀ η K α γ d₀ : ℝ) (p : JetPrototype.Phase) : ℝ :=
  ∑' i : Index, term s₀ η K α γ d₀ i p

theorem term_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ : ℝ) (i : Index) (p : JetPrototype.Phase) : 0 ≤ term s₀ η K α γ d₀ i p :=
  density_nonneg hK (DatumBounds.scale_pos hs₀ _).le
    (mul_nonneg hd₀ (pow_nonneg (DatumBounds.scale_pos hs₀ _).le _)) η α γ i.2 p

theorem term_integrable {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η)
    (hK : 0 ≤ K) (hd₀ : 0 < d₀) (α γ : ℝ) (i : Index) :
    Integrable (term s₀ η K α γ d₀ i) (spaceVolume.prod volume) :=
  density_integrable hη hK (DatumBounds.scale_pos hs₀ _).le
    (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α γ i.2

theorem term_entropy_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) (i : Index) :
    Integrable (fun p => entropy (term s₀ η K α γ d₀ i p)) (spaceVolume.prod volume) :=
  JetPrototypeEntropy.density_entropy_integrable hη hK hγ (DatumBounds.scale_pos hs₀ _)
    (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α i.2

theorem term_measurable (s₀ η K α γ d₀ : ℝ) (i : Index) :
    Measurable (term s₀ η K α γ d₀ i) := measurable_density _ _ _ _ _ _ _

private def label (i : Index) : JetLattice.Label := ⟨i.1, i.2, 0⟩

private theorem in_enlargement {s₀ η K α γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    {i : Index} {p : JetPrototype.Phase} (hp : term s₀ η K α γ d₀ i p ≠ 0) :
    PlaneChart.join p.1.1 p.1.2 ∈ JetLattice.spatialEnlargement s₀ η 0 (label i) := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.1 + 1)
  have hsp := JetSupport.initial_spatial_support η K α γ _ _ i.2 hp
  constructor
  · change transverse (PlaneChart.join p.1.1 p.1.2) - JetLattice.transverseShift 0 ∈
      enlargement η (jetScale s₀ η i.1) i.2
    have hz : JetLattice.transverseShift 0 = 0 := by ext k; simp [JetLattice.transverseShift]
    rw [PlaneChart.transverse_join, hz, sub_zero]
    exact Metric.mem_cthickening_of_dist_le p.1.1 p.1.1 _ _ hsp.1
      (by simpa [jetScale] using (enlargementWidth_pos hη hs).le)
  · simpa [label, JetLattice.axialShift, PlaneChart.axial_join] using
      (show |p.1.2| ≤ 1 / 8 + 2 * (0 : ℝ) + 1 / 16 by linarith [hsp.2])

theorem term_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase)
    (i j : Index) (hij : i ≠ j) (hi : term s₀ η K α γ d₀ i p ≠ 0) :
    term s₀ η K α γ d₀ j p = 0 := by
  by_contra hj
  have he := JetLattice.common_point_label hs₀ hsmax hη hηmax (by norm_num : (0 : ℝ) ≤ 1 / 32)
    (in_enlargement hs₀ hη hi) (in_enlargement hs₀ hη hj)
  apply hij
  exact Prod.ext (congrArg JetLattice.Label.annulus he) (congrArg JetLattice.Label.positive he)

theorem term_summable {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    Summable (fun i => term s₀ η K α γ d₀ i p) :=
  JetSeries.summable_single_support (term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p)

theorem entropy_datum {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    entropy (datum s₀ η K α γ d₀ p) = ∑' i, entropy (term s₀ η K α γ d₀ i p) :=
  JetSeries.entropy_tsum (term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p)

theorem summable_bool_extension {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (hs : Summable f) :
    Summable (fun i : Index => f i.1) := by
  apply (summable_prod_of_nonneg (fun i => hf i.1)).mpr
  constructor
  · intro j
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  · simpa only [tsum_fintype, Fintype.sum_bool] using hs.add hs

theorem mass_summable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) :
    Summable (fun i : Index => ∫ p, term s₀ η K α γ d₀ i p ∂spaceVolume.prod volume) := by
  have hs : Summable (fun j => (8 * Real.pi * K / γ) * jetScale s₀ η j ^ 2) := by
    exact ((summable_nat_add_iff 1).mpr (DatumBounds.summable_scale_sq s₀ hη)).mul_left _
  apply Summable.of_nonneg_of_le
    (fun i => integral_nonneg (term_nonneg hs₀ hK hd₀.le η α γ i))
    (fun i => density_mass_bound hη.le hηmax hK hγ (DatumBounds.scale_pos hs₀ _)
      (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α i.2)
    (summable_bool_extension (fun j => by positivity) hs)

theorem entropy_summable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) :
    Summable (fun i : Index => ∫ p, entropy (term s₀ η K α γ d₀ i p) ∂spaceVolume.prod volume) := by
  have hs : Summable (fun j => JetEntropyBound.constant K γ d₀ *
      (jetScale s₀ η j ^ 2 * (1 + |Real.log (jetScale s₀ η j)|))) := by
    exact ((summable_nat_add_iff 1).mpr (DatumBounds.summable_entropyBound hs₀ hη)).mul_left _
  apply Summable.of_nonneg_of_le
    (fun i => integral_nonneg (fun p => entropy_nonneg (term_nonneg hs₀ hK.le hd₀.le η α γ i p)))
    (fun i => ?_) (summable_bool_extension (fun j => by
      have := JetEntropyBound.constant_nonneg hK.le hγ.le d₀
      positivity) hs)
  simpa only [mul_assoc, term, jetScale] using JetEntropyBound.prototype_entropy_bound hη.le hηmax hK hγ
    (DatumBounds.scale_pos hs₀ _) hd₀ α i.2

theorem datum_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) : Integrable (datum s₀ η K α γ d₀) (spaceVolume.prod volume) :=
  JetSeries.integrable_nonnegative_series (term_measurable s₀ η K α γ d₀)
    (term_integrable hs₀ hη.le hK hd₀ α γ) (term_nonneg hs₀ hK hd₀.le η α γ)
    (term_summable hs₀ hsmax hη hηmax K α γ d₀) (mass_summable hs₀ hη hηmax hK hγ hd₀ α)

theorem datum_entropy_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) :
    Integrable (fun p => entropy (datum s₀ η K α γ d₀ p)) (spaceVolume.prod volume) := by
  simp_rw [entropy_datum hs₀ hsmax hη hηmax]
  apply JetSeries.integrable_nonnegative_series
    (fun i => JetPrototypeEntropy.measurable_entropy (term_measurable s₀ η K α γ d₀ i))
    (term_entropy_integrable hs₀ hη.le hK.le hγ hd₀ α)
    (fun i p => entropy_nonneg (term_nonneg hs₀ hK.le hd₀.le η α γ i p))
    (fun p => JetSeries.summable_single_support ?_)
    (entropy_summable hs₀ hη hηmax hK hγ hd₀ α)
  intro i j hij hi
  have ht : term s₀ η K α γ d₀ i p ≠ 0 := by
    intro h
    exact hi (by simp [h, entropy])
  simp [term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p i j hij ht, entropy]

end BoltzmannNonuniqueness.JetDatum

end

end

section

/-! # Mass, energy, and entropy of the full cold datum -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetDatum

namespace BoltzmannNonuniqueness.JetDatumMoments

theorem datum_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ : ℝ) (p : JetPrototype.Phase) : 0 ≤ datum s₀ η K α γ d₀ p :=
  tsum_nonneg (fun i => term_nonneg hs₀ hK hd₀ η α γ i p)

theorem mass_eq_sum {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) :
    (∫ p, datum s₀ η K α γ d₀ p ∂spaceVolume.prod volume) =
      ∑' i, ∫ p, term s₀ η K α γ d₀ i p ∂spaceVolume.prod volume :=
  JetSeries.integral_nonnegative_series (term_integrable hs₀ hη.le hK hd₀ α γ)
    (term_nonneg hs₀ hK hd₀.le η α γ) (mass_summable hs₀ hη hηmax hK hγ hd₀ α)

theorem entropy_eq_sum {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) :
    (∫ p, entropy (datum s₀ η K α γ d₀ p) ∂spaceVolume.prod volume) =
      ∑' i, ∫ p, entropy (term s₀ η K α γ d₀ i p) ∂spaceVolume.prod volume := by
  simp_rw [entropy_datum hs₀ hsmax hη hηmax]
  exact JetSeries.integral_nonnegative_series (term_entropy_integrable hs₀ hη.le hK.le hγ hd₀ α)
    (fun i p => entropy_nonneg (term_nonneg hs₀ hK.le hd₀.le η α γ i p))
    (entropy_summable hs₀ hη hηmax hK hγ hd₀ α)

theorem thermal_width_le {s₀ η d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hd₀ : 0 ≤ d₀) (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (j : ℕ) :
    d₀ * jetScale s₀ η j ^ 10 ≤ 1 / 64 := by
  have hs : jetScale s₀ η j ≤ 1 / 8 := by
    change DatumBounds.scale s₀ η (j + 1) ≤ _
    calc
      _ ≤ DatumBounds.scale s₀ η 0 := scale_antitone hs₀.le hη (Nat.zero_le (j + 1))
      _ = s₀ := by simp [DatumBounds.scale]
      _ ≤ _ := hsmax
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (DatumBounds.scale_pos hs₀ _).le hs 10) hd₀).trans hwidth

theorem datum_support_two {s₀ η d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hd₀ : 0 < d₀) (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (K γ : ℝ) (p : JetPrototype.Phase)
    (hp : 2 ≤ ‖p.2‖) : datum s₀ η K α γ d₀ p = 0 := by
  have hz : ∀ i, term s₀ η K α γ d₀ i p = 0 := by
    intro i
    by_contra hi
    have hv := JetSupport.density_support_two
      (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _))
      (thermal_width_le hs₀ hsmax hη hd₀.le hwidth i.1) hα hαmax η K γ _ i.2 hi
    exact (not_lt_of_ge hp) hv
  simp only [datum, hz, tsum_zero]

theorem datum_energy_integrable {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    Integrable (fun p => datum s₀ η K α γ d₀ p * ‖p.2‖ ^ 2) (spaceVolume.prod volume) := by
  have hi := datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α
  apply (hi.mul_const 4).mono'
  · exact hi.aestronglyMeasurable.mul (continuous_snd.norm.pow 2).aestronglyMeasurable
  · filter_upwards [] with p
    have hn := datum_nonneg hs₀ hK hd₀.le η α γ p
    rw [Real.norm_of_nonneg (mul_nonneg hn (sq_nonneg _))]
    by_cases hv : 2 ≤ ‖p.2‖
    · rw [datum_support_two hs₀ hsmax hη.le hd₀ hwidth hα hαmax K γ p hv]
      simp
    · have hv' : ‖p.2‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg p.2]
      exact mul_le_mul_of_nonneg_left hv' hn

theorem datum_entropyMoment_integrable {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    Integrable (fun p => datum s₀ η K α γ d₀ p *
      (1 + ‖p.2‖ ^ 2 + |Real.log (datum s₀ η K α γ d₀ p)|)) (spaceVolume.prod volume) := by
  convert ((datum_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ α).add
    (datum_energy_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ hwidth hα hαmax)).add
    (datum_entropy_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α) using 1
  ext p
  simp only [Pi.add_apply, entropy]
  ring

end BoltzmannNonuniqueness.JetDatumMoments

end

end

section

/-! # Pointwise stabilization of the annular truncations -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetDatum

namespace BoltzmannNonuniqueness.JetTruncation

def truncated (s₀ η K α γ d₀ : ℝ) (N : ℕ) (p : JetPrototype.Phase) : ℝ :=
  ∑' i : Index, if i.1 < N then term s₀ η K α γ d₀ i p else 0

theorem truncated_measurable (s₀ η K α γ d₀ : ℝ) (N : ℕ) :
    Measurable (truncated s₀ η K α γ d₀ N) := by
  apply Measurable.tsum
  intro i
  by_cases hi : i.1 < N
  · simpa only [ite_eq_left hi] using term_measurable s₀ η K α γ d₀ i
  · simp only [ite_eq_right hi]
    exact measurable_const

theorem truncated_at_nonzero {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (N : ℕ)
    (p : JetPrototype.Phase) {i : Index} (hi : term s₀ η K α γ d₀ i p ≠ 0) :
    truncated s₀ η K α γ d₀ N p = if i.1 < N then datum s₀ η K α γ d₀ p else 0 := by
  have hz : ∀ j, j ≠ i → term s₀ η K α γ d₀ j p = 0 :=
    fun j hj => term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p i j hj.symm hi
  have hd : datum s₀ η K α γ d₀ p = term s₀ η K α γ d₀ i p := tsum_eq_single i hz
  unfold truncated
  rw [tsum_eq_single i]
  · rw [hd]
  · intro j hj
    simp only [hz j hj, ite_self]

theorem truncated_eq_or_zero {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (N : ℕ)
    (p : JetPrototype.Phase) :
    truncated s₀ η K α γ d₀ N p = datum s₀ η K α γ d₀ p ∨
      truncated s₀ η K α γ d₀ N p = 0 := by
  by_cases h : ∃ i, term s₀ η K α γ d₀ i p ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [truncated_at_nonzero hs₀ hsmax hη hηmax K α γ d₀ N p hi]
    split_ifs <;> simp
  · have hz : ∀ i, term s₀ η K α γ d₀ i p = 0 := fun i => not_ne_iff.mp (not_exists.mp h i)
    right
    simp only [truncated, hz, ite_self, tsum_zero]

theorem eventually_truncated_eq {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    ∀ᶠ N in atTop, truncated s₀ η K α γ d₀ N p = datum s₀ η K α γ d₀ p := by
  by_cases h : ∃ i, term s₀ η K α γ d₀ i p ≠ 0
  · obtain ⟨i, hi⟩ := h
    apply eventually_atTop.mpr
    refine ⟨i.1 + 1, fun N hN => ?_⟩
    rw [truncated_at_nonzero hs₀ hsmax hη hηmax K α γ d₀ N p hi, ite_eq_left (by omega)]
  · have hz : ∀ i, term s₀ η K α γ d₀ i p = 0 := fun i => not_ne_iff.mp (not_exists.mp h i)
    apply Eventually.of_forall
    intro N
    simp only [truncated, datum, hz, ite_self, tsum_zero]

theorem truncated_tendsto {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    Tendsto (fun N => truncated s₀ η K α γ d₀ N p) atTop (𝓝 (datum s₀ η K α γ d₀ p)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_truncated_eq hs₀ hsmax hη hηmax K α γ d₀ p] with N hN
  exact hN.symm

end BoltzmannNonuniqueness.JetTruncation

end

end

section

/-! # The free cold core in Eulerian coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem flight_add (t r : ℝ) (p : JetPrototype.Phase) :
    flight t (flight r p) = flight (t + r) p := by
  apply Prod.ext
  · apply Prod.ext
    · dsimp only [flight]
      module
    · dsimp only [flight]
      ring
  · rfl

@[simp] theorem flight_zero (p : JetPrototype.Phase) : flight 0 p = p := by
  simp only [flight, zero_smul, zero_mul, add_zero, Prod.eta]

@[simp] theorem flight_neg (t : ℝ) (p : JetPrototype.Phase) : flight t (flight (-t) p) = p := by
  rw [flight_add, add_neg_cancel, flight_zero]

@[simp] theorem neg_flight (t : ℝ) (p : JetPrototype.Phase) : flight (-t) (flight t p) = p := by
  rw [flight_add, neg_add_cancel, flight_zero]

def free (η K α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  density η K α γ s d a (flight (-t) p)

theorem free_along (η K α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    free η K α γ s d t a (flight t p) = density η K α γ s d a p := by
  rw [free, neg_flight]

theorem free_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ t : ℝ) (a : Bool) (p : JetPrototype.Phase) : 0 ≤ free η K α γ s d t a p :=
  density_nonneg hK hs hd η α γ a _

theorem free_le_barrier {K d α γ s t : ℝ} (hK : 0 ≤ K) (hd : 0 < d) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 < t) (htmax : t ≤ 2)
    (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    free η K α γ s d t a p ≤ barrier η K α γ s d t a p := by
  have h := free_core_le_barrier hK hd hα hγ hs ht htmax η a (flight (-t) p)
  simpa only [free, flight_neg] using h

theorem measurable_free (η K α γ s d t : ℝ) (a : Bool) :
    Measurable (free η K α γ s d t a) := by
  apply (measurable_density η K α γ s d a).comp
  unfold flight transverse axial
  fun_prop

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # Joint measurability of the transported cold core -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem measurable_joint_free (η K α γ s d : ℝ) (a : Bool) :
    Measurable (fun p : ℝ × JetPrototype.Phase => free η K α γ s d p.1 a p.2) := by
  apply (JetPrototype.measurable_density η K α γ s d a).comp
  unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
  fun_prop

theorem measurable_uncurried_free (η K α γ s d : ℝ) (a : Bool) :
    Measurable (fun p : (ℝ × JetPrototype.Space) × Velocity =>
      free η K α γ s d p.1.1 a (p.1.2,p.2)) := by
  let f : ((ℝ × JetPrototype.Space) × Velocity) → ℝ × JetPrototype.Phase :=
    fun p => (p.1.1,(p.1.2,p.2))
  have hf : Measurable f :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  simpa only [Function.comp_def,f] using (measurable_joint_free η K α γ s d a).comp hf

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # Convergence in mass, energy, and absolute entropy of the actual annular truncations -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetDatum
open BoltzmannNonuniqueness.JetTruncation
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetConvergence

theorem selection_L1_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ} {f : X → ℝ} (hF : ∀ N, AEStronglyMeasurable (F N) μ)
    (hf : Integrable f μ) (hsel : ∀ N x, F N x = f x ∨ F N x = 0)
    (heq : ∀ x, ∀ᶠ N in atTop, F N x = f x) :
    Tendsto (fun N => ∫ x, ‖F N x - f x‖ ∂μ) atTop (𝓝 0) := by
  have hB : ∀ N, ∀ᵐ x ∂μ, ‖‖F N x - f x‖‖ ≤ ‖f x‖ := by
    intro N
    apply Eventually.of_forall
    intro x
    rcases hsel N x with hNx | hNx <;> simp [hNx]
  have hL : ∀ᵐ x ∂μ, Tendsto (fun N => ‖F N x - f x‖) atTop (𝓝 (0 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [heq x] with N hNx
    simp only [hNx, sub_self, norm_zero]
  simpa only [integral_zero, Pi.sub_apply] using
    tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun N => ((hF N).sub hf.aestronglyMeasurable).norm) hf.norm hB hL

theorem mass_L1_tendsto {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) :
    Tendsto (fun N => ∫ p, ‖truncated s₀ η K α γ d₀ N p - datum s₀ η K α γ d₀ p‖
      ∂spaceVolume.prod volume) atTop (𝓝 0) :=
  selection_L1_tendsto (fun N => (truncated_measurable s₀ η K α γ d₀ N).aestronglyMeasurable)
    (datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
    (truncated_eq_or_zero hs₀ hsmax hη hηmax K α γ d₀)
    (eventually_truncated_eq hs₀ hsmax hη hηmax K α γ d₀)

theorem entropy_L1_tendsto {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) :
    Tendsto (fun N => ∫ p,
      ‖entropy (truncated s₀ η K α γ d₀ N p) - entropy (datum s₀ η K α γ d₀ p)‖
      ∂spaceVolume.prod volume) atTop (𝓝 0) := by
  apply selection_L1_tendsto
    (fun N => (JetPrototypeEntropy.measurable_entropy
      (truncated_measurable s₀ η K α γ d₀ N)).aestronglyMeasurable)
    (datum_entropy_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
  · intro N p
    rcases truncated_eq_or_zero hs₀ hsmax hη hηmax K α γ d₀ N p with h | h
    · exact Or.inl (congrArg entropy h)
    · exact Or.inr (by simp only [h, entropy, zero_mul])
  · intro p
    filter_upwards [eventually_truncated_eq hs₀ hsmax hη hηmax K α γ d₀ p] with N hN
    exact congrArg entropy hN

theorem energy_L1_tendsto {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    Tendsto (fun N => ∫ p,
      ‖truncated s₀ η K α γ d₀ N p * ‖p.2‖ ^ 2 - datum s₀ η K α γ d₀ p * ‖p.2‖ ^ 2‖
      ∂spaceVolume.prod volume) atTop (𝓝 0) := by
  apply selection_L1_tendsto
    (fun N => ((truncated_measurable s₀ η K α γ d₀ N).aestronglyMeasurable.mul
      (continuous_snd.norm.pow 2).aestronglyMeasurable))
    (JetDatumMoments.datum_energy_integrable hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax)
  · intro N p
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rcases truncated_eq_or_zero hs₀ hsmax hη hηmax K α γ d₀ N p with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, zero_mul])
  · intro p
    filter_upwards [eventually_truncated_eq hs₀ hsmax hη hηmax K α γ d₀ p] with N hN
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [hN]

end BoltzmannNonuniqueness.JetConvergence

end

end

section

/-! # Gaussian summation over the actual periodic-copy distances -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetLatticeTail

theorem pointwise_bound {η α s t B : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (hB : 0 ≤ B)
    (γ : ℝ) (a : Bool) (x : Velocity) (n : Lattice) :
    Real.exp (-B * distanceSquared η α γ s t a (shifted x n)) ≤
      JetLatticeProduct.product (B / 2) 1 x n := by
  rw [JetLatticeProduct.product_eq_exp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (coordinate_bound hη hηmax hα hαmax hs hsmax ht htmax γ a x n) hB
  unfold gap at h
  linarith

theorem sum_bound {η α s t B : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (hB : 2 ≤ B)
    (γ : ℝ) (a : Bool) (x : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    (∑' n : Lattice, ENNReal.ofReal (Real.exp (-B * distanceSquared η α γ s t a (shifted x n)))) ≤
      ENNReal.ofReal (JetLatticeGaussian.constant ^ 3) := by
  apply (ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal
    (pointwise_bound hη hηmax hα hαmax hs hsmax ht htmax (by linarith) γ a x n))).trans
  exact JetLatticeProduct.sum_le (by linarith) (by norm_num) hx

def outside (η s t : ℝ) (a : Bool) (x : Velocity) (n : Lattice) : Prop :=
  ¬((shifted x n).1 ∈ enlargement η s a ∧ |(shifted x n).2| ≤ 1 / 8 + 2 * t + 1 / 16)

theorem escaped_sum_bound {η α s t B : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (hB : 2 ≤ B)
    (γ : ℝ) (a : Bool) (x : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    (∑' n : Lattice, {n | outside η s t a x n}.indicator
      (fun n => ENNReal.ofReal (Real.exp (-(2 * B) * distanceSquared η α γ s t a (shifted x n)))) n) ≤
      ENNReal.ofReal (Real.exp (-B * (enlargementWidth η s) ^ 2)) *
        ENNReal.ofReal (JetLatticeGaussian.constant ^ 3) := by
  have hpoint (n : Lattice) : {n | outside η s t a x n}.indicator
      (fun n => ENNReal.ofReal (Real.exp (-(2 * B) * distanceSquared η α γ s t a (shifted x n)))) n ≤
      ENNReal.ofReal (Real.exp (-B * (enlargementWidth η s) ^ 2)) *
        ENNReal.ofReal (Real.exp (-B * distanceSquared η α γ s t a (shifted x n))) := by
    by_cases hn : outside η s t a x n
    · rw [Set.indicator_of_mem hn, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hdist := JetEscapeGeometry.distance_lower_bound hη hηmax hα hαmax hs hsmax ht γ a (shifted x n) hn
      nlinarith [mul_le_mul_of_nonneg_left hdist (by linarith : 0 ≤ B)]
    · rw [Set.indicator_of_notMem hn]
      exact bot_le
  apply (ENNReal.tsum_le_tsum hpoint).trans
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul' le_rfl (sum_bound hη hηmax hα hαmax hs hsmax ht htmax hB γ a x hx)

end BoltzmannNonuniqueness.JetLatticeTail

end

end

section

/-! # A uniform, explicit coefficient for cold-color comparison -/

noncomputable section

open BoltzmannNonuniqueness.JetBarrierCollision

namespace BoltzmannNonuniqueness.JetComparisonCoefficient

def coefficient (K : ℝ) : ℝ := 8 * frequencyConstant * K + 1

theorem coefficient_ge_one {K : ℝ} (hK : 0 ≤ K) : 1 ≤ coefficient K := by
  unfold coefficient
  nlinarith [mul_nonneg frequencyConstant_nonneg hK]

theorem linear_le_quadratic {d : ℝ} (hd : 0 < d) (r : ℝ) :
    d + r ≤ 2 * d * (1 + (7 / 8 : ℝ) * r ^ 2 / d ^ 2) := by
  have he : 2 * d * (1 + (7 / 8 : ℝ) * r ^ 2 / d ^ 2) =
      (2 * d ^ 2 + (7 / 4 : ℝ) * r ^ 2) / d := by
    field_simp
    ring
  rw [he]
  apply (le_div_iff₀ hd).mpr
  nlinarith [sq_nonneg (d - r)]

theorem comparison_bound {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) (r : ℝ) :
    4 * frequencyConstant * (K / s) * (d + r) ≤
      (coefficient K * d / s) * (1 + (7 / 8 : ℝ) * r ^ 2 / d ^ 2) := by
  have hq : 0 ≤ 1 + (7 / 8 : ℝ) * r ^ 2 / d ^ 2 := by positivity
  have hL : 8 * frequencyConstant * K ≤ coefficient K := by unfold coefficient; linarith
  calc
    _ ≤ 4 * frequencyConstant * (K / s) *
        (2 * d * (1 + (7 / 8 : ℝ) * r ^ 2 / d ^ 2)) :=
      mul_le_mul_of_nonneg_left (linear_le_quadratic hd r)
        (mul_nonneg (mul_nonneg (by norm_num) frequencyConstant_nonneg) (div_nonneg hK hs.le))
    _ = (8 * frequencyConstant * K) * ((d / s) * (1 + (7 / 8 : ℝ) * r ^ 2 / d ^ 2)) := by ring
    _ ≤ coefficient K * ((d / s) * (1 + (7 / 8 : ℝ) * r ^ 2 / d ^ 2)) :=
      mul_le_mul_of_nonneg_right hL (mul_nonneg (div_nonneg hd.le hs.le) hq)
    _ = _ := by ring

end BoltzmannNonuniqueness.JetComparisonCoefficient

end

end

section

/-! # The completed-square estimate for the barrier logarithmic derivative -/

noncomputable section

namespace BoltzmannNonuniqueness.JetBarrierDifferential

def spatialTerm (t y z dy dz : ℝ) : ℝ :=
  (y ^ 2 + z ^ 2) / t ^ 2 - 2 * (y * dy + z * dz) / t

theorem spatialTerm_lower {t : ℝ} (ht : t ≠ 0) (y z dy dz : ℝ) :
    -(dy ^ 2 + dz ^ 2) ≤ spatialTerm t y z dy dz := by
  have he : spatialTerm t y z dy dz + (dy ^ 2 + dz ^ 2) =
      (y / t - dy) ^ 2 + (z / t - dz) ^ 2 := by
    unfold spatialTerm
    field_simp
    ring
  have h := add_nonneg (sq_nonneg (y / t - dy)) (sq_nonneg (z / t - dz))
  rw [← he] at h
  linarith

theorem logarithmic_derivative_lower {t d W c : ℝ} (ht : 0 < t) (htmax : t ≤ 2)
    (hd : 0 < d) (hc : 0 ≤ c) (r y z dy dz : ℝ) (hgrad : dy ^ 2 + dz ^ 2 ≤ W) :
    1 + (7 / 8 : ℝ) * W / d ^ 2 ≤
      1 + (W + 2 * (2 - t) * c * r ^ 2) / d ^ 2 + spatialTerm t y z dy dz / (8 * d ^ 2) := by
  have hsp := spatialTerm_lower ht.ne' y z dy dz
  have hl : -W ≤ spatialTerm t y z dy dz := by linarith
  have hs := div_le_div_of_nonneg_right hl (by positivity : 0 ≤ 8 * d ^ 2)
  have hk : W / d ^ 2 ≤ (W + 2 * (2 - t) * c * r ^ 2) / d ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg d)
    have hpos : 0 ≤ 2 * (2 - t) * c * r ^ 2 := by positivity
    linarith
  calc
    _ = 1 + W / d ^ 2 + -W / (8 * d ^ 2) := by field_simp; ring
    _ ≤ _ := add_le_add (add_le_add le_rfl hk) hs

end BoltzmannNonuniqueness.JetBarrierDifferential

end

end

section

/-! # The escaped Gaussian barrier summed over all periodic copies -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedCopies

def halfRate (d t : ℝ) : ℝ := 1 / (16 * d ^ 2 * t)

theorem halfRate_large {d t : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 16)
    (ht : 0 < t) (htmax : t ≤ 1) : 2 ≤ halfRate d t := by
  unfold halfRate
  apply (le_div_iff₀ (by positivity : 0 < 16 * d ^ 2 * t)).mpr
  have hsq : d ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ hd.le hdmax 2
  have hprod := mul_le_mul hsq htmax ht.le (by norm_num : (0 : ℝ) ≤ (1 / 16) ^ 2)
  nlinarith

theorem rate_identity {d₀ s t : ℝ} (hd₀ : 0 < d₀) (hs : 0 < s) (ht : 0 < t) (η : ℝ) :
    halfRate (d₀ * s ^ 10) t * (enlargementWidth η s) ^ 2 =
      (JetEscapedBarrier.rate η d₀ / 2) / (s ^ 16 * t) := by
  unfold halfRate enlargementWidth JetEscapedBarrier.rate
  field_simp
  ring

theorem copy_sum_bound {η K α s d₀ t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (hd₀ : 0 < d₀) (hwidth : d₀ * s ^ 10 ≤ 1 / 16) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (γ : ℝ) (a : Bool) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    (∑' n : Lattice, {n | outside η s t a x n}.indicator
      (fun n => ENNReal.ofReal (barrier η K α γ s (d₀ * s ^ 10) t a (shifted x n, v))) n) ≤
      ENNReal.ofReal (JetEscapedBarrier.coefficient α K d₀ *
        JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) s t * Real.exp (-4 * ‖v‖ ^ 2)) *
          ENNReal.ofReal (JetLatticeGaussian.constant ^ 3) := by
  have hd : 0 < d₀ * s ^ 10 := by positivity
  let B := halfRate (d₀ * s ^ 10) t
  let A := JetGaussianEscape.constant α * (K / s) * ((d₀ * s ^ 10) ^ 3)⁻¹ * Real.exp (-4 * ‖v‖ ^ 2)
  have hA : 0 ≤ A := by
    unfold A JetGaussianEscape.constant
    have := JetThermalKernel.bound_pos
    positivity
  have hB : 2 ≤ B := halfRate_large hd hwidth ht (by linarith)
  have he (D : ℝ) : -(1 / 8 : ℝ) * D / ((d₀ * s ^ 10) ^ 2 * t) = -(2 * B) * D := by
    unfold B halfRate
    field_simp
    ring
  have hpoint (n : Lattice) : {n | outside η s t a x n}.indicator
      (fun n => ENNReal.ofReal (barrier η K α γ s (d₀ * s ^ 10) t a (shifted x n, v))) n ≤
      ENNReal.ofReal A * {n | outside η s t a x n}.indicator
        (fun n => ENNReal.ofReal (Real.exp (-(2 * B) * distanceSquared η α γ s t a (shifted x n)))) n := by
    by_cases hn : outside η s t a x n
    · rw [indicator_of_mem hn, indicator_of_mem hn, ← ENNReal.ofReal_mul hA]
      apply ENNReal.ofReal_le_ofReal
      have hb := JetGaussianEscape.barrier_velocity_decay hK hα hs hd hwidth (by linarith : t ≤ 1)
        η γ a (shifted x n) v
      rw [he] at hb
      apply hb.trans_eq
      unfold A
      ring
    · have hn' : n ∉ {n | outside η s t a x n} := hn
      simp only [indicator_of_notMem hn', mul_zero, le_refl]
  apply (ENNReal.tsum_le_tsum hpoint).trans
  rw [ENNReal.tsum_mul_left]
  apply (mul_le_mul' le_rfl (escaped_sum_bound hη hηmax hα hαmax hs hsmax ht.le htmax hB γ a x hx)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul hA]
  congr 1
  congr 1
  rw [neg_mul, show B * (enlargementWidth η s) ^ 2 =
    (JetEscapedBarrier.rate η d₀ / 2) / (s ^ 16 * t) from rate_identity hd₀ hs ht η, ← neg_div]
  unfold A JetEscapedBarrier.coefficient JetEscapePower.tail
  field_simp

end BoltzmannNonuniqueness.JetEscapedCopies

end

end

section

/-! # The cold datum on the actual unit spatial torus -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetPeriodicDatum

def spatialMap (x : Velocity) : Space := (transverse x, axial x)

def phaseMap (p : Velocity × Velocity) : JetPrototype.Phase := (spatialMap p.1, p.2)

def pullback (f : JetPrototype.Phase → ℝ) (p : Phase) : ℝ :=
  f (phaseMap (TorusChart.phaseRepresentative p))

def datum (s₀ η K α γ d₀ : ℝ) : Density := pullback (JetDatum.datum s₀ η K α γ d₀)

theorem spatialMap_measurePreserving : MeasurePreserving spatialMap volume spaceVolume := by
  convert Measure.measurePreserving_swap.comp split_measurePreserving using 1
  funext x
  change (transverse x, axial x) = (split x).swap
  rw [split_apply]
  rfl

theorem phaseMap_measurePreserving : MeasurePreserving phaseMap volume (spaceVolume.prod volume) :=
  spatialMap_measurePreserving.prod (MeasurePreserving.id (volume : Measure Velocity))

theorem integrable_pullback {f : JetPrototype.Phase → ℝ}
    (hf : Integrable f (spaceVolume.prod volume)) : Integrable (pullback f) := by
  have hl := phaseMap_measurePreserving.integrable_comp_of_integrable hf
  exact TorusChart.phase_measurePreserving.integrable_comp_of_integrable hl.restrict

theorem finiteEntropy {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    FiniteEntropyDatum (datum s₀ η K α γ d₀) := by
  refine ⟨Filter.Eventually.of_forall (fun p => ?_), ?_, ?_⟩
  · exact JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  · exact (integrable_pullback (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ α)).1
  · exact integrable_pullback
      (JetDatumMoments.datum_entropyMoment_integrable hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax)

theorem boundedVelocitySupport {s₀ η d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hd₀ : 0 < d₀) (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (K γ : ℝ) :
    BoundedVelocitySupport (datum s₀ η K α γ d₀) := by
  refine ⟨2, by norm_num, Filter.Eventually.of_forall (fun p hp => ?_)⟩
  exact JetDatumMoments.datum_support_two hs₀ hsmax hη hd₀ hwidth hα hαmax K γ _ hp.le

end BoltzmannNonuniqueness.JetPeriodicDatum

end

end

end OAI
