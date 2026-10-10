import OAI.MathematicalPhysics.Boltzmann.Branching.HotQuadraticGain
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionMeasure
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarrierKinetic
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

section

/-! # The full logarithmic barrier derivative along free flights -/

noncomputable section

open MeasureTheory Filter
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetDistanceDerivative
open BoltzmannNonuniqueness.JetBarrierKinetic
open BoltzmannNonuniqueness.JetBarrierDifferential
open BoltzmannNonuniqueness.AxialTransport

namespace BoltzmannNonuniqueness.JetLogDerivative

def Y (η s : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ → ℝ :=
  transverseDistance η s a p.1.1 (transverse p.2)

def Z (α γ s : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ → ℝ :=
  axialDistance (sign a) α γ s p.1.2 (axial p.2)

def rawExponent (η α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) : ℝ :=
  t - (2 - t) * squaredError (sign a) α γ s p.1.2 p.2 t / d ^ 2 -
    ((Y η s a p t ^ 2 + Z α γ s a p t ^ 2) / t) / (8 * d ^ 2)

def logSlope (η α γ s d t dy dz : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  1 + (squaredError (sign a) α γ s p.1.2 p.2 t +
    2 * (2 - t) * compression (sign a) α γ s p.1.2 (axial p.2) t *
      (axial p.2 - flightVelocity (sign a) α γ s p.1.2 (axial p.2) t) ^ 2) / d ^ 2 +
    spatialTerm t (Y η s a p t) (Z α γ s a p t) dy dz / (8 * d ^ 2)

theorem rawExponent_eq (η α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) :
    rawExponent η α γ s d a p t =
      JetBarrier.exponent η α γ s d t a (JetBarrier.flight t p) := by
  unfold rawExponent JetBarrier.exponent JetBarrier.flight JetBarrier.centerVelocity
  rw [JetCoreFlight.norm_sq_error]
  unfold squaredError flightVelocity JetBarrier.distanceSquared Y Z transverseDistance axialDistance flightFoot
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem rawExponent_derivative {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (η : ℝ) (a : Bool) (p : JetPrototype.Phase)
    {dy dz : ℝ} (hy : HasDerivAt (Y η s a p) dy t) (hz : HasDerivAt (Z α γ s a p) dz t) :
    HasDerivAt (rawExponent η α γ s d a p) (logSlope η α γ s d t dy dz a p) t := by
  have hk := kineticExponent_derivative (σ := sign a) hα hγ hs ht.le p.1.2 d p.2
  have hsum := (hy.pow 2).add (hz.pow 2)
  have hq := (hsum.div (hasDerivAt_id t) ht.ne').div_const (8 * d ^ 2)
  have h := ((hasDerivAt_id t).add hk).sub hq
  convert h using 1
  · funext r
    unfold rawExponent
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, id]
    ring
  · unfold logSlope spatialTerm
    dsimp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.div_apply, id]
    field_simp
    ring

theorem distance_gradient_bound {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η : ℝ) (a : Bool) (p : JetPrototype.Phase)
    {dy dz : ℝ} (hy : HasDerivAt (Y η s a p) dy t) (hz : HasDerivAt (Z α γ s a p) dz t) :
    dy ^ 2 + dz ^ 2 ≤ squaredError (sign a) α γ s p.1.2 p.2 t := by
  have hbY : |dy| ≤ ‖transverse p.2‖ := by
    simpa only [Real.norm_eq_abs, coe_nnnorm] using
      hy.le_of_lipschitz (transverse_lipschitz η s a p.1.1 (transverse p.2))
  have hbZ := axial_derivative_bound hα hγ hs ht p.1.2 (axial p.2) hz.differentiableAt
  change |deriv (Z α γ s a p) t| ≤ _ at hbZ
  rw [hz.deriv] at hbZ
  have hden : 1 ≤ 1 + t * AxialDerivative.A α γ s
      (flightFoot (sign a) α γ s p.1.2 (axial p.2) t) := by
    have hA := AxialDerivative.A_nonneg hα hγ hs.le
      (flightFoot (sign a) α γ s p.1.2 (axial p.2) t)
    linarith [mul_nonneg ht hA]
  rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hden)] at hbZ
  have hbZ' := hbZ.trans (div_le_self (abs_nonneg _) hden)
  unfold squaredError
  nlinarith [sq_abs dy, sq_abs dz,
    sq_abs (axial p.2 - flightVelocity (sign a) α γ s p.1.2 (axial p.2) t),
    abs_nonneg dy, abs_nonneg dz, norm_nonneg (transverse p.2)]

theorem logSlope_lower {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 2) (η : ℝ) (a : Bool)
    (p : JetPrototype.Phase) {dy dz : ℝ}
    (hy : HasDerivAt (Y η s a p) dy t) (hz : HasDerivAt (Z α γ s a p) dz t) :
    1 + (7 / 8 : ℝ) * squaredError (sign a) α γ s p.1.2 p.2 t / d ^ 2 ≤
      logSlope η α γ s d t dy dz a p :=
  logarithmic_derivative_lower ht htmax hd
    (compression_nonneg hα hγ hs ht.le (sign a) p.1.2 (axial p.2)) _ _ _ _ _
    (distance_gradient_bound hα hγ hs ht.le η a p hy hz)

theorem ae_logarithmic_derivative {α γ s d : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    ∀ᵐ t, 0 < t → t ≤ 2 →
      HasDerivAt (rawExponent η α γ s d a p) (deriv (rawExponent η α γ s d a p) t) t ∧
        1 + (7 / 8 : ℝ) * squaredError (sign a) α γ s p.1.2 p.2 t / d ^ 2 ≤
          deriv (rawExponent η α γ s d a p) t := by
  filter_upwards [transverse_ae_derivative_bound η s a p.1.1 (transverse p.2),
    axial_ae_differentiable (σ := sign a) hα hγ hs p.1.2 (axial p.2)] with t hy hz ht htmax
  have hY : HasDerivAt (Y η s a p) (deriv (Y η s a p) t) t := hy.1.hasDerivAt
  have hZ : HasDerivAt (Z α γ s a p) (deriv (Z α γ s a p) t) t := (hz ht).hasDerivAt
  have he := rawExponent_derivative hα hγ hs hd ht η a p hY hZ
  refine ⟨he.differentiableAt.hasDerivAt, ?_⟩
  rw [he.deriv]
  exact logSlope_lower hα hγ hs hd ht htmax η a p hY hZ

end BoltzmannNonuniqueness.JetLogDerivative

end

end

section

/-! # The differential lower bound for the actual transported Gaussian barrier -/

noncomputable section

open MeasureTheory Filter
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLogDerivative
open BoltzmannNonuniqueness.JetBarrierKinetic

namespace BoltzmannNonuniqueness.JetBarrierDerivative

def along (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) : ℝ :=
  barrier η K α γ s d t a (flight t p)

def amplitude (K s d : ℝ) : ℝ :=
  (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹

theorem along_eq (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) :
    along η K α γ s d a p t = amplitude K s d * Real.exp (rawExponent η α γ s d a p t) := by
  rw [rawExponent_eq]
  rfl

theorem squaredError_eq (α γ s : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) :
    squaredError (sign a) α γ s p.1.2 p.2 t = ‖JetCoreFlight.error α γ s t a p‖ ^ 2 := by
  rw [JetCoreFlight.error, JetCoreFlight.norm_sq_error]
  rfl

/-- Manuscript inequality (4.7), almost everywhere on each free characteristic. -/
theorem ae_barrier_derivative {K α γ s d : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    ∀ᵐ t, 0 < t → t ≤ 2 →
      HasDerivAt (along η K α γ s d a p) (deriv (along η K α γ s d a p) t) t ∧
        (1 + (7 / 8 : ℝ) * ‖JetCoreFlight.error α γ s t a p‖ ^ 2 / d ^ 2) *
          along η K α γ s d a p t ≤ deriv (along η K α γ s d a p) t := by
  filter_upwards [ae_logarithmic_derivative hα hγ hs hd η a p] with t ht htpos htmax
  obtain ⟨he, hle⟩ := ht htpos htmax
  have hfun : (fun r => amplitude K s d * Real.exp (rawExponent η α γ s d a p r)) =
      along η K α γ s d a p := funext (fun r => (along_eq η K α γ s d a p r).symm)
  have hb := he.exp.const_mul (amplitude K s d)
  rw [hfun] at hb
  have hderiv : deriv (along η K α γ s d a p) t =
      along η K α γ s d a p t * deriv (rawExponent η α γ s d a p) t := by
    rw [hb.deriv, along_eq]
    ring
  refine ⟨hb.differentiableAt.hasDerivAt, ?_⟩
  rw [hderiv]
  have hn : 0 ≤ along η K α γ s d a p t := barrier_nonneg hK hs.le hd.le η α γ t a _
  rw [squaredError_eq] at hle
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hle hn

end BoltzmannNonuniqueness.JetBarrierDerivative

end

end

section

/-! # The actual free-core plus Gaussian supersolution -/

noncomputable section

open MeasureTheory Filter
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetFreeTransport
open BoltzmannNonuniqueness.JetBarrierCollision
open BoltzmannNonuniqueness.JetComparisonCoefficient

namespace BoltzmannNonuniqueness.JetSupersolution

def epsilon (K s d : ℝ) : ℝ := coefficient K * d / s

def U (η K α γ s d t : ℝ) (a : Bool) (p : JetPrototype.Phase) : ℝ :=
  free η K α γ s d t a p + epsilon K s d * barrier η K α γ s d t a p

theorem epsilon_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) :
    0 ≤ epsilon K s d :=
  div_nonneg (mul_nonneg (zero_le_one.trans (coefficient_ge_one hK)) hd.le) hs.le

theorem nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (η α γ t : ℝ) (a : Bool) (p : JetPrototype.Phase) : 0 ≤ U η K α γ s d t a p :=
  add_nonneg (free_nonneg hK hs.le hd.le η α γ t a p)
    (mul_nonneg (epsilon_nonneg hK hs hd) (barrier_nonneg hK hs.le hd.le η α γ t a p))

theorem le_twice_barrier {K s d α γ t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : epsilon K s d ≤ 1) (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    U η K α γ s d t a p ≤ 2 * barrier η K α γ s d t a p := by
  have hf := free_le_barrier hK hd hα hγ hs ht (htmax.trans (by norm_num)) η a p
  have hm := mul_le_mul_of_nonneg_right hε (barrier_nonneg hK hs.le hd.le η α γ t a p)
  unfold U
  linarith

theorem measurable_velocity {d : ℝ} (hd : 0 < d) (η K α γ s t : ℝ) (a : Bool) (x : Space) :
    Measurable (fun v => U η K α γ s d t a (x, v)) := by
  exact ((measurable_free η K α γ s d t a).comp (measurable_const.prodMk measurable_id)).add
    (measurable_const.mul (JetBarrierCollision.measurable_velocity hd η K α γ s t a x))

theorem gain_bound {K s d α γ t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : epsilon K s d ≤ 1) (η : ℝ) (a : Bool) (x : Space) (z : Position) (v : Velocity) :
    gain (fun p => U η K α γ s d t a (x, p.2)) z v ≤
      (4 * frequencyConstant * (K / s) * (d + ‖v - centerVelocity α γ s t a x‖)) *
        barrier η K α γ s d t a (x, v) := by
  have hm := integrable_gain hK hs hd htmax η α γ a x v
  have hmon := GainOrder.gain_mono (measurable_velocity hd η K α γ s t a x)
    (fun w => nonneg hK hs hd η α γ t a (x, w))
    (fun w => le_twice_barrier hK hs hd hα hγ ht htmax hε η a (x, w)) v z
    (GainOrder.integrable_const_mul 2 v hm)
  have hb := frequency_bound hK hs hd ht htmax η α γ a x z v
  have hprod := mul_le_mul_of_nonneg_left hb (barrier_nonneg hK hs.le hd.le η α γ t a (x, v))
  calc
    _ ≤ _ := hmon
    _ = 4 * gain (fun p => barrier η K α γ s d t a (x, p.2)) z v := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
        GainOrder.gain_const_mul 2 (fun w => barrier η K α γ s d t a (x, w)) v z
    _ = 4 * (barrier η K α γ s d t a (x, v) *
        frequency (fun p => barrier η K α γ s d t a (x, p.2)) z v) := by
      rw [self_gain hK hs hd htmax η α γ a x z v]
    _ ≤ _ := by nlinarith only [hprod]

def along (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) : ℝ :=
  U η K α γ s d t a (flight t p)

theorem along_eq (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) (t : ℝ) :
    along η K α γ s d a p t = density η K α γ s d a p +
      epsilon K s d * JetBarrierDerivative.along η K α γ s d a p t := by
  simp only [along, U, free_along, JetBarrierDerivative.along]

/-- The supersolution inequality used in Proposition `prop:cold-control`.
The only smallness condition here is the explicit thermal-width condition. -/
theorem ae_supersolution {K s d α γ : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hε : epsilon K s d ≤ 1)
    (η : ℝ) (a : Bool) (p : JetPrototype.Phase) (z : Position) :
    ∀ᵐ t, 0 < t → t ≤ 1 →
      HasDerivAt (along η K α γ s d a p) (deriv (along η K α γ s d a p) t) t ∧
        gain (fun q => U η K α γ s d t a ((flight t p).1, q.2)) z p.2 ≤
          deriv (along η K α γ s d a p) t := by
  filter_upwards [JetBarrierDerivative.ae_barrier_derivative hK hα hγ hs hd η a p]
    with t ht htpos htmax
  obtain ⟨hm, hdm⟩ := ht htpos (htmax.trans (by norm_num))
  have hf : (fun r => density η K α γ s d a p +
      epsilon K s d * JetBarrierDerivative.along η K α γ s d a p r) =
      along η K α γ s d a p := funext (fun r => (along_eq η K α γ s d a p r).symm)
  have hu := (hm.const_mul (epsilon K s d)).const_add (density η K α γ s d a p)
  rw [hf] at hu
  refine ⟨hu.differentiableAt.hasDerivAt, ?_⟩
  rw [hu.deriv]
  have hg := gain_bound hK hs hd hα hγ htpos htmax hε η a (flight t p).1 z p.2
  have hc := comparison_bound hK hs hd ‖JetCoreFlight.error α γ s t a p‖
  have hn := barrier_nonneg hK hs.le hd.le η α γ t a (flight t p)
  have hcm := mul_le_mul_of_nonneg_right hc hn
  have hdd := mul_le_mul_of_nonneg_left hdm (epsilon_nonneg hK hs hd)
  change _ ≤ epsilon K s d * deriv (JetBarrierDerivative.along η K α γ s d a p) t
  exact hg.trans (hcm.trans (by simpa only [epsilon, mul_assoc, JetBarrierDerivative.along] using hdd))

end BoltzmannNonuniqueness.JetSupersolution

end

end

section

/-! # The full velocity measure under the thermal-coordinate map -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreJacobian

namespace BoltzmannNonuniqueness.JetCoreMeasure

theorem jacobian_measurable {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (σ d z : ℝ) : Measurable (jacobian σ α γ s d t z) := by
  have hf : Measurable (foot σ α γ s t) := (foot_lipschitzWith hα hγ hs ht).continuous.measurable
  have hS := JetAxialWeight.continuous_S.measurable
  unfold jacobian A sourceFoot
  fun_prop

theorem axial_measurePreserving {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) :
    MeasurePreserving (axialMap σ α γ s d t z)
      (volume.withDensity (fun w => ENNReal.ofReal (jacobian σ α γ s d t z w))) volume := by
  let hhome := axialHomeomorph hα hγ hs ht hd.ne' σ z
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℝ)
    (s := univ) MeasurableSet.univ.nullMeasurableSet
    (fun w _ => (axialMap_derivative hα hγ hs ht σ d z w).hasDerivWithinAt.hasFDerivWithinAt)
    hhome.injective.injOn
  have hr : axialMap σ α γ s d t z '' univ = univ := Set.image_univ ▸ hhome.surjective.range_eq
  rw [hr, Measure.restrict_univ] at hm
  simp only [ContinuousLinearMap.det_toSpanSingleton] at hm
  change Measure.map (axialMap σ α γ s d t z)
    (volume.withDensity (fun w => ENNReal.ofReal (|jacobian σ α γ s d t z w|))) = volume at hm
  simp only [abs_of_pos (jacobian_pos hα hγ hs hd ht σ z _)] at hm
  exact ⟨hhome.continuous.measurable, hm⟩

theorem transverse_measurePreserving {d : ℝ} (hd : 0 < d) :
    MeasurePreserving (fun w : Transverse => d • w)
      (ENNReal.ofReal (d ^ 2) • (volume : Measure Transverse)) volume := by
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_smul _ (by fun_prop), Measure.map_addHaar_smul volume hd.ne', smul_smul]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← ENNReal.ofReal_mul (sq_nonneg d), abs_of_pos (inv_pos.mpr (sq_pos_of_pos hd)),
    mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hd)), ENNReal.ofReal_one, one_smul]

def parameterMeasure (σ α γ s d t z : ℝ) : Measure (Transverse × ℝ) :=
  (ENNReal.ofReal (d ^ 2) • (volume : Measure Transverse)).prod
    (volume.withDensity (fun w => ENNReal.ofReal (jacobian σ α γ s d t z w)))

def velocityMap (σ α γ s d t z : ℝ) (w : Transverse × ℝ) : Velocity :=
  PlaneChart.join (d • w.1) (axialMap σ α γ s d t z w.2)

theorem velocity_measurePreserving {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) :
    MeasurePreserving (velocityMap σ α γ s d t z) (parameterMeasure σ α γ s d t z) volume := by
  change MeasurePreserving (SheetMeasures.join ∘
    Prod.map (fun w : Transverse => d • w) (axialMap σ α γ s d t z)) _ _
  exact HotRectangleDensity.join_measurePreserving.comp
    ((transverse_measurePreserving hd).prod (axial_measurePreserving hα hγ hs hd ht σ z))

theorem parameterMeasure_eq {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (σ d z : ℝ) :
    parameterMeasure σ α γ s d t z =
      ((volume : Measure Transverse).prod volume).withDensity
        (fun w => ENNReal.ofReal (d ^ 2 * jacobian σ α γ s d t z w.2)) := by
  unfold parameterMeasure
  rw [← withDensity_const, prod_withDensity measurable_const (jacobian_measurable hα hγ hs ht σ d z).ennreal_ofReal]
  congr 1
  funext w
  rw [ENNReal.ofReal_mul (sq_nonneg d)]


theorem map_withDensity {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    ((parameterMeasure σ α γ s d t z).withDensity
      (fun w => f (velocityMap σ α γ s d t z w))).map (velocityMap σ α γ s d t z) =
      volume.withDensity f := by
  have h := velocity_measurePreserving hα hγ hs hd ht σ z
  ext B hB
  rw [Measure.map_apply h.measurable hB,
    withDensity_apply _ (hB.preimage h.measurable), withDensity_apply _ hB,
    ← lintegral_indicator (hB.preimage h.measurable), ← lintegral_indicator hB]
  convert h.lintegral_comp (hf.indicator hB) using 1
  apply lintegral_congr
  intro w
  rfl

end BoltzmannNonuniqueness.JetCoreMeasure

end

end

section

/-! # Cutoff-independent loss bounds on a cold free core -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.CollisionCutoff

theorem frequency_le_majorant_ae (b : ℝ) {f g : Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w) (hfg : ∀ᵐ w, f w ≤ g w)
    (v : Velocity) (hg : Integrable (fun w => ‖v-w‖*g w)) :
    frequency b f v ≤ 2*Real.pi*(∫ w, ‖v-w‖*g w) := by
  have hn (w : Velocity) : 0 ≤ rate b v w*f w := mul_nonneg (rate_nonneg b v w) (hfn w)
  have hb : ∀ᵐ w, rate b v w*f w ≤ ‖v-w‖*g w := by
    filter_upwards [hfg] with w hw
    have hr : rate b v w ≤ ‖v-w‖ := by
      unfold rate
      split_ifs <;> simp only [le_refl,norm_nonneg]
    exact (mul_le_mul_of_nonneg_right hr (hfn w)).trans
      (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
  have hi : Integrable (fun w => rate b v w*f w) := by
    apply hg.mono' ((measurable_rate b v).mul hfm).aestronglyMeasurable
    filter_upwards [hb] with w hw
    change ‖rate b v w*f w‖ ≤ ‖v-w‖*g w
    rwa [Real.norm_of_nonneg (hn w)]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hi hg hb) (by positivity)

theorem frequency_le_majorant (b : ℝ) {f g : Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w)
    (v : Velocity) (hg : Integrable (fun w => ‖v-w‖*g w)) :
    frequency b f v ≤ 2*Real.pi*(∫ w, ‖v-w‖*g w) := by
  have hn (w : Velocity) : 0 ≤ rate b v w*f w := mul_nonneg (rate_nonneg b v w) (hfn w)
  have hb (w : Velocity) : rate b v w*f w ≤ ‖v-w‖*g w := by
    have hr : rate b v w ≤ ‖v-w‖ := by
      unfold rate
      split_ifs <;> simp only [le_refl,norm_nonneg]
    exact (mul_le_mul_of_nonneg_right hr (hfn w)).trans
      (mul_le_mul_of_nonneg_left (hfg w) (norm_nonneg _))
  have hi : Integrable (fun w => rate b v w*f w) := by
    apply hg.mono' ((measurable_rate b v).mul hfm).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun w => by
      change ‖rate b v w*f w‖ ≤ ‖v-w‖*g w
      rw [Real.norm_of_nonneg (hn w)]
      exact hb w)
  exact mul_le_mul_of_nonneg_left (integral_mono hi hg hb) (by positivity)

end CollisionCutoff

namespace JetSupersolution

theorem cutoff_frequency_bound {K s d α γ t : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (ht : 0 < t) (htmax : t ≤ 1) (hε : epsilon K s d ≤ 1)
    (η b : ℝ) (a : Bool) (x : Space) {f : Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w)
    (hfU : ∀ w, f w ≤ U η K α γ s d t a (x,w)) (v : Velocity) :
    CollisionCutoff.frequency b f v ≤
      2*JetBarrierCollision.frequencyConstant*(K/s)*
        (d+‖v-JetBarrier.centerVelocity α γ s t a x‖) := by
  let B : Density := fun p => JetBarrier.barrier η K α γ s d t a (x,p.2)
  have hB : Integrable (fun w => ‖v-w‖*B (0,w)) := by
    have hc := JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x
    have hβ : 0 < 2-t := by linarith
    apply integrable_frequency_integrand
    · simpa only [B,JetBarrierCollision.barrier_eq_density hd] using
        GaussianFrequency.integrable hβ hd
          (JetBarrierCollision.massScale η K α γ s d t a x)
          (JetBarrier.centerVelocity α γ s t a x)
    · simpa only [B,JetBarrierCollision.barrier_eq_density hd] using
        GaussianFrequency.first_moment_integrable hc hβ hd
          (JetBarrier.centerVelocity α γ s t a x)
  have h2B : Integrable (fun w => ‖v-w‖*(2*B (0,w))) := by
    convert hB.const_mul 2 using 1
    funext w
    ring
  have hf2 (w) : f w ≤ 2*B (0,w) :=
    (hfU w).trans (le_twice_barrier hK hs hd hα hγ ht htmax hε η a (x,w))
  have h := CollisionCutoff.frequency_le_majorant b hfm hfn hf2 v h2B
  have he : 2*Real.pi*(∫ w, ‖v-w‖*(2*B (0,w))) = 2*frequency B 0 v := by
    have hf : (fun w => ‖v-w‖*(2*B (0,w))) = (fun w => 2*(‖v-w‖*B (0,w))) := by
      funext w
      ring
    rw [hf,integral_const_mul]
    unfold frequency
    ring
  rw [he] at h
  have hbar := JetBarrierCollision.frequency_bound hK hs hd ht htmax η α γ a x 0 v
  change frequency B 0 v ≤ _ at hbar
  nlinarith only [h,hbar]

theorem core_cutoff_frequency_bound {K s d α γ t : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (ht : 0 < t) (htmax : t ≤ 1) (hε : epsilon K s d ≤ 1)
    (η b : ℝ) (a : Bool) (x : Space) {f : Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w)
    (hfU : ∀ w, f w ≤ U η K α γ s d t a (x,w)) {v : Velocity}
    (hv : ‖v-JetBarrier.centerVelocity α γ s t a x‖ ≤ d) :
    CollisionCutoff.frequency b f v ≤ 4*JetBarrierCollision.frequencyConstant*K*d/s := by
  have h := cutoff_frequency_bound hK hs hd hα hγ ht htmax hε η b a x hfm hfn hfU v
  have hc : 0 ≤ 2*JetBarrierCollision.frequencyConstant*(K/s) :=
    mul_nonneg (mul_nonneg (by norm_num) JetBarrierCollision.frequencyConstant_nonneg)
      (div_nonneg hK hs.le)
  calc
    _ ≤ _ := h
    _ ≤ 2*JetBarrierCollision.frequencyConstant*(K/s)*(d+d) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hv) hc
    _ = _ := by ring

theorem core_frequency_along {K s d α γ t : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (ht : 0 < t) (htmax : t ≤ 1) (hε : epsilon K s d ≤ 1)
    (η b : ℝ) (a : Bool) (p : JetPrototype.Phase)
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) {f : Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w)
    (hfU : ∀ w, f w ≤ U η K α γ s d t a ((JetBarrier.flight t p).1,w)) :
    CollisionCutoff.frequency b f p.2 ≤ 4*JetBarrierCollision.frequencyConstant*K*d/s := by
  apply core_cutoff_frequency_bound hK hs hd hα hγ ht htmax hε η b a
    (JetBarrier.flight t p).1 hfm hfn hfU
  exact (JetCoreFlight.error_lt_width hd hα hγ hs ht.le η K a hp).le

end JetSupersolution
end BoltzmannNonuniqueness

end

end

section

/-! # The exact compressed density of a transported cold core -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreJacobian
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermal_argument {α d : ℝ} (hα : 0 ≤ α) (hd : d ≠ 0)
    (γ s t : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    d⁻¹ • (velocityMap (sign a) α γ s d t x.2 w -
      center α γ s a (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2)) =
      SheetMeasures.join w := by
  have ha := axialMap_spec hα (sign a) γ s d t x.2 w.2
  apply split.injective
  rw [split_apply, split_apply]
  apply Prod.ext
  · change d⁻¹ * (axial (velocityMap (sign a) α γ s d t x.2 w) -
        axial (center α γ s a (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2))) =
        axial (SheetMeasures.join w)
    simp only [velocityMap, JetPrototype.center, PlaneChart.axial_join]
    change d⁻¹ * (axialMap (sign a) α γ s d t x.2 w.2 -
        AxialFlow.profile (sign a) α γ s (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2)) = w.2
    have hz : axialMap (sign a) α γ s d t x.2 w.2 -
        AxialFlow.profile (sign a) α γ s (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) =
        d * w.2 := by linarith
    rw [hz]
    field_simp
  · have ht : ∀ (c : ℝ) (v : Velocity), transverse (c • v) = c • transverse v := by
      intro c v
      apply (WithLp.ext_iff 2).mpr
      rfl
    rw [ht, PlaneChart.transverse_sub]
    simp only [velocityMap, JetPrototype.center, PlaneChart.transverse_join, sub_zero, smul_smul,
      inv_mul_cancel₀ hd, one_smul]
    exact (PlaneChart.transverse_join w.1 w.2).symm

def compressed (K α γ s t ζ : ℝ) : ℝ :=
  K * S (γ * ζ / s) / (s + t * α * γ * S (γ * ζ / s))

def weight (η K α γ s d t : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) : ℝ :=
  (JetGeometry.mask η s a).indicator (fun _ => (1 : ℝ)) (x.1 - t • (d • w.1)) *
    (Ioo (-(1 / 8 : ℝ)) (1 / 8)).indicator (compressed K α γ s t)
      (sourceFoot (sign a) α γ s d t x.2 w.2) * JetThermalKernel.J (SheetMeasures.join w)

theorem density_identity {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    (d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2) *
      JetFreeTransport.free η K α γ s d t a (x, velocityMap (sign a) α γ s d t x.2 w) =
      weight η K α γ s d t a x w := by
  have hthermal := thermal_argument hα hd.ne' γ s t a x w
  have hfoot := sourceFoot_eq (sign a) α γ s d t x.2 w.2
  have hf : JetFreeTransport.free η K α γ s d t a
        (x, velocityMap (sign a) α γ s d t x.2 w) =
      spatial η K γ s a (x.1 - t • (d • w.1),
        x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) *
        ((d ^ 3)⁻¹ * JetThermalKernel.J (SheetMeasures.join w)) := by
    unfold JetFreeTransport.free density JetThermalLaw.density JetThermalLaw.scaled
    simp only [JetBarrier.flight, velocityMap, PlaneChart.transverse_join, PlaneChart.axial_join,
      neg_smul, neg_mul, ← sub_eq_add_neg]
    unfold velocityMap at hthermal
    rw [hthermal]
  rw [hf]
  unfold spatial axialAmplitude weight
  rw [hfoot]
  by_cases hy : x.1 - t • (d • w.1) ∈ JetGeometry.mask η s a
  · by_cases hz : x.2 - t * axialMap (sign a) α γ s d t x.2 w.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simp only [indicator_of_mem hy, indicator_of_mem hz, one_mul]
      have hc : d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2 *
          ((K / s) * S (γ * (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) / s) * (d ^ 3)⁻¹) =
          compressed K α γ s t (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) := by
        have ha := AxialDerivative.A_nonneg hα hγ hs.le
          (sourceFoot (sign a) α γ s d t x.2 w.2)
        have hden : 1 + t * AxialDerivative.A α γ s
            (sourceFoot (sign a) α γ s d t x.2 w.2) ≠ 0 := by positivity
        have hden' : s + t * α * γ * S
            (γ * (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) / s) ≠ 0 := by
          have := S_pos (γ * (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) / s)
          positivity
        unfold jacobian AxialDerivative.A at hden ⊢
        rw [hfoot] at hden ⊢
        unfold compressed
        field_simp
      calc
        _ = (d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2 *
          ((K / s) * S (γ * (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) / s) * (d ^ 3)⁻¹)) *
          JetThermalKernel.J (SheetMeasures.join w) := by ring
        _ = _ := by rw [hc]
    · simp only [indicator_of_notMem hz, mul_zero, zero_mul]
  · simp only [indicator_of_notMem hy, mul_zero, zero_mul]


theorem compressed_nonneg {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (ζ : ℝ) :
    0 ≤ compressed K α γ s t ζ := by
  unfold compressed
  have := (S_pos (γ * ζ / s)).le
  positivity

theorem compressed_bound {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t) (ζ : ℝ) :
    compressed K α γ s t ζ ≤ (K * max 1 (α * γ)⁻¹) / (s + t) := by
  have h := compression_bound hK hs ht (mul_pos hα hγ)
    (S_pos (γ * ζ / s)).le (S_le_one (γ * ζ / s))
  simpa only [compressed, mul_assoc] using h

theorem weight_bound {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    weight η K α γ s d t a x w ≤
      ((K * max 1 (α * γ)⁻¹) / (s + t)) * JetThermalKernel.J (SheetMeasures.join w) := by
  have hc := compressed_bound hK hα hγ hs ht
    (sourceFoot (sign a) α γ s d t x.2 w.2)
  have hj := JetThermalKernel.J_nonneg (SheetMeasures.join w)
  unfold weight
  by_cases hy : x.1 - t • (d • w.1) ∈ JetGeometry.mask η s a
  · by_cases hz : sourceFoot (sign a) α γ s d t x.2 w.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simp only [indicator_of_mem hy, indicator_of_mem hz, one_mul]
      exact mul_le_mul_of_nonneg_right hc hj
    · simp only [indicator_of_notMem hz, mul_zero, zero_mul]
      positivity
  · simp only [indicator_of_notMem hy, zero_mul]
    positivity

theorem measure_identity {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) (x : Space) :
    (((volume : Measure Transverse).prod volume).withDensity
      (fun w => ENNReal.ofReal (weight η K α γ s d t a x w))).map
        (velocityMap (sign a) α γ s d t x.2) =
      volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) := by
  have hf : Measurable (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) :=
    ((JetFreeTransport.measurable_free η K α γ s d t a).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hmap := JetCoreMeasure.map_withDensity hα hγ hs hd ht (sign a) x.2 hf
  have hmeas := (velocity_measurePreserving hα hγ hs hd ht (sign a) x.2).measurable
  have heq : (parameterMeasure (sign a) α γ s d t x.2).withDensity
      (fun w => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a
        (x, velocityMap (sign a) α γ s d t x.2 w))) =
      ((volume : Measure Transverse).prod volume).withDensity
        (fun w => ENNReal.ofReal (weight η K α γ s d t a x w)) := by
    rw [parameterMeasure_eq hα hγ hs ht]
    have hjm : Measurable (fun w : Transverse × ℝ =>
        ENNReal.ofReal (d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2)) :=
      (measurable_const.mul ((jacobian_measurable hα hγ hs ht (sign a) d x.2).comp
        measurable_snd)).ennreal_ofReal
    have hfg : Measurable (fun w => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a
        (x, velocityMap (sign a) α γ s d t x.2 w))) := hf.comp hmeas
    rw [← withDensity_mul _ hjm hfg]
    congr 1
    funext w
    change ENNReal.ofReal (d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2) * _ = _
    rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg d)
      (jacobian_pos hα hγ hs hd ht (sign a) x.2 w.2).le),
      density_identity hα hγ hs hd ht]
  rw [heq] at hmap
  exact hmap

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Fixed-scale uniform bounds for the cold envelope -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetEnvelopeBound

def amplitude (K s d : ℝ) : ℝ :=
  Real.exp 4 * JetThermalKernel.bound * (K / s) * (d ^ 3)⁻¹

theorem amplitude_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) :
    0 ≤ amplitude K s d := by
  unfold amplitude
  have := JetThermalKernel.bound_pos
  positivity

theorem barrier_le {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    JetBarrier.barrier η K α γ s d t a p ≤ amplitude K s d := by
  have hD : 0 ≤ JetBarrier.distanceSquared η α γ s t a p.1 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he : JetBarrier.exponent η α γ s d t a p ≤ 1 := by
    unfold JetBarrier.exponent
    have hk : 0 ≤ (2 - t) * ‖p.2 - JetBarrier.centerVelocity α γ s t a p.1‖ ^ 2 / d ^ 2 := by
      apply div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _)
    have hx : 0 ≤ (1 / 8 : ℝ) * JetBarrier.distanceSquared η α γ s t a p.1 / (d ^ 2 * t) :=
      div_nonneg (mul_nonneg (by norm_num) hD) (by positivity)
    linarith
  unfold JetBarrier.barrier amplitude
  have hc : 0 ≤ Real.exp 3 * JetThermalKernel.bound * (K / s) * (d ^ 3)⁻¹ := by
    have := JetThermalKernel.bound_pos
    positivity
  calc
    _ ≤ (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹ * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hc
    _ = _ := by
      have he4 : Real.exp (3 : ℝ) * Real.exp 1 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
      calc
        _ = (Real.exp 3 * Real.exp 1) * JetThermalKernel.bound * (K / s) * (d ^ 3)⁻¹ := by ring
        _ = _ := by rw [he4]

def gainAmplitude (K α s d : ℝ) (v : Velocity) : ℝ :=
  (4 * JetBarrierCollision.frequencyConstant * (K / s) * (d + ‖v‖ + (1 + α))) * amplitude K s d

theorem gainAmplitude_nonneg {K α s d : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hs : 0 < s) (hd : 0 < d) (v : Velocity) : 0 ≤ gainAmplitude K α s d v := by
  unfold gainAmplitude
  have := JetBarrierCollision.frequencyConstant_nonneg
  have := amplitude_nonneg hK hs hd
  positivity

theorem gain_bound {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    BoltzmannNonuniqueness.gain (fun p => JetSupersolution.U η K α γ s d t a (x, p.2)) 0 v ≤
      gainAmplitude K α s d v := by
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := x.2) hα
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  rw [hsiga] at hu
  have hcenter : ‖JetBarrier.centerVelocity α γ s t a x‖ ≤ 1 + α := by
    have hn := PlaneChart.norm_join_sq 0 (AxialFlow.velocity (sign a) α γ s t x.2)
    simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] at hn
    change ‖JetBarrier.centerVelocity α γ s t a x‖ ^ 2 = _ at hn
    nlinarith [sq_abs (AxialFlow.velocity (sign a) α γ s t x.2),
      abs_nonneg (AxialFlow.velocity (sign a) α γ s t x.2),
      norm_nonneg (JetBarrier.centerVelocity α γ s t a x)]
  have hnorm : ‖v - JetBarrier.centerVelocity α γ s t a x‖ ≤ ‖v‖ + (1 + α) :=
    (norm_sub_le _ _).trans (add_le_add le_rfl hcenter)
  have hfreq : 0 ≤ 4 * JetBarrierCollision.frequencyConstant * (K / s) := by
    have := JetBarrierCollision.frequencyConstant_nonneg
    positivity
  apply (JetSupersolution.gain_bound hK hs hd hα hγ ht htmax hε η a x 0 v).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith :
    d + ‖v - JetBarrier.centerVelocity α γ s t a x‖ ≤ d + ‖v‖ + (1 + α)) hfreq)
    (barrier_le hK hs hd ht htmax η α γ a (x, v))
    (JetBarrier.barrier_nonneg hK hs.le hd.le η α γ t a (x, v))
    (mul_nonneg hfreq (by positivity))

theorem integrable_gain {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    Integrable (GainOrder.integrand (fun w => JetSupersolution.U η K α γ s d t a (x, w)) v)
      ((volume : Measure Velocity).prod sphereArea) :=
  GainOrder.integrable_of_le (JetSupersolution.measurable_velocity hd η K α γ s t a x)
    (fun w => JetSupersolution.nonneg hK hs hd η α γ t a (x, w))
    (fun w => JetSupersolution.le_twice_barrier hK hs hd hα hγ ht htmax hε η a (x, w)) v
    (GainOrder.integrable_const_mul 2 v (JetBarrierCollision.integrable_gain hK hs hd htmax η α γ a x v))

theorem cutoff_gain_bound {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η b : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    CollisionCutoff.gain b (fun w => JetSupersolution.U η K α γ s d t a (x, w)) v ≤
      gainAmplitude K α s d v :=
  (CollisionCutoff.gain_le b (JetSupersolution.measurable_velocity hd η K α γ s t a x)
    (fun w => JetSupersolution.nonneg hK hs hd η α γ t a (x, w)) v 0
    (integrable_gain hK hα hγ hs hd ht htmax hε η a x v)).trans
    (gain_bound hK hα hγ hs hd ht htmax hε η a x v)

theorem U_le_H {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η q : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    JetSupersolution.U η K α γ s d t a (x, v) ≤
      (2 * JetGaussianEscape.constant α * (K / s) * (d ^ 3)⁻¹ * tiltConstant) * H q v := by
  have hD : 0 ≤ JetBarrier.distanceSquared η α γ s t a x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he : Real.exp (-(1 / 8 : ℝ) * JetBarrier.distanceSquared η α γ s t a x / (d ^ 2 * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hD) (by positivity)
  have hg : Real.exp (-4 * ‖v‖ ^ 2) ≤ tiltConstant * H q v :=
    (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖v‖])).trans (JetGaussianEscape.gaussian_le_hot q v)
  have hc : 0 ≤ JetGaussianEscape.constant α * (K / s) * (d ^ 3)⁻¹ := by
    unfold JetGaussianEscape.constant
    have := JetThermalKernel.bound_pos
    positivity
  have hb := JetGaussianEscape.barrier_velocity_decay hK hα hs hd hdmax htmax η γ a x v
  calc
    _ ≤ 2 * JetBarrier.barrier η K α γ s d t a (x, v) :=
      JetSupersolution.le_twice_barrier hK hs hd hα hγ ht htmax hε η a (x, v)
    _ ≤ 2 * (JetGaussianEscape.constant α * (K / s) * (d ^ 3)⁻¹ * (1 * (tiltConstant * H q v))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hb.trans (by
        rw [mul_assoc _ (Real.exp _) (Real.exp _)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul he hg (Real.exp_nonneg _) (by norm_num)) hc)
    _ = _ := by ring

end BoltzmannNonuniqueness.JetEnvelopeBound

end

end

section

/-! # Absolute continuity of the barrier on positive-time intervals -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.AxialTransport
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetDistanceDerivative
open BoltzmannNonuniqueness.JetLogDerivative
open BoltzmannNonuniqueness.JetBarrierKinetic
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetBarrierRegularity

theorem profile_lipschitz {α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (σ : ℝ) :
    LipschitzWith (Real.toNNReal (α * γ / s)) (profile σ α γ s) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun z => (profile_derivative σ α γ s z).differentiableAt)
  intro z
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, (profile_derivative σ α γ s z).deriv,
    abs_of_nonneg (A_nonneg hα hγ hs.le z), Real.coe_toNNReal _ (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (JetAxialWeight.S_le_one _)

private theorem square_ac {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => f t ^ 2) a b := by
  convert hf.mul hf using 1
  funext t
  exact pow_two _

private theorem exp_ac {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => Real.exp (f t)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨L, hL⟩ := (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ 1 Real.exp (Icc (-C) C)).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  apply hL.comp_absolutelyContinuousOnInterval _ hf
  intro t ht
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hC t ht)

theorem flightFoot_ac {σ α γ s a b : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b) (z v : ℝ) :
    AbsolutelyContinuousOnInterval (flightFoot σ α γ s z v) a b := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  apply (flightFoot_lipschitzOn (σ := σ) hα hγ hs z v).mono
  intro t ht
  exact ha.trans ((uIcc_of_le hab ▸ ht).1)

theorem flightVelocity_ac {σ α γ s a b : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ha : 0 ≤ a) (hab : a ≤ b) (z v : ℝ) :
    AbsolutelyContinuousOnInterval (flightVelocity σ α γ s z v) a b := by
  have h := (profile_lipschitz hα hγ hs σ).comp_absolutelyContinuousOnInterval
    (flightFoot_ac (σ := σ) hα hγ hs ha hab z v)
  convert h using 1
  funext t
  exact velocity_spec hα

theorem rawExponent_ac {α γ s a b : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) (η d : ℝ) (label : Bool) (p : JetPrototype.Phase) :
    AbsolutelyContinuousOnInterval (rawExponent η α γ s d label p) a b := by
  have hid : AbsolutelyContinuousOnInterval (fun t : ℝ => t) a b :=
    contDiff_id.contDiffOn.absolutelyContinuousOnInterval
  have hconst (c : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hv := flightVelocity_ac (σ := sign label) hα hγ hs ha.le hab p.1.2 (axial p.2)
  have herr : AbsolutelyContinuousOnInterval (squaredError (sign label) α γ s p.1.2 p.2) a b := by
    exact (hconst _).add (square_ac ((hconst (axial p.2)).sub hv))
  have hy : AbsolutelyContinuousOnInterval (Y η s label p) a b :=
    (transverse_lipschitz η s label p.1.1 (transverse p.2)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hz : AbsolutelyContinuousOnInterval (Z α γ s label p) a b :=
    (lipschitz_infDist_pt (Icc (-(1 / 8 : ℝ)) (1 / 8))).comp_absolutelyContinuousOnInterval
      (flightFoot_ac hα hγ hs ha.le hab p.1.2 (axial p.2))
  have hinv : AbsolutelyContinuousOnInterval (fun t : ℝ => t⁻¹) a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    apply contDiffOn_id.inv
    intro t ht
    exact (ha.trans_le ((uIcc_of_le hab ▸ ht).1)).ne'
  have hkin := (((hconst 2).sub hid).mul herr).const_mul (d ^ 2)⁻¹
  have hspace := (((square_ac hy).add (square_ac hz)).mul hinv).const_mul (8 * d ^ 2)⁻¹
  convert (hid.sub hkin).sub hspace using 1
  funext t
  unfold rawExponent
  dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
  simp only [div_eq_mul_inv]
  ring

theorem barrier_ac {α γ s a b : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) (η K d : ℝ) (label : Bool) (p : JetPrototype.Phase) :
    AbsolutelyContinuousOnInterval (JetBarrierDerivative.along η K α γ s d label p) a b := by
  have h := (exp_ac (rawExponent_ac hα hγ hs ha hab η d label p)).const_mul
    (JetBarrierDerivative.amplitude K s d)
  convert h using 1
  funext t
  exact JetBarrierDerivative.along_eq η K α γ s d label p t

end BoltzmannNonuniqueness.JetBarrierRegularity

end

end

section

/-! # Joint measurability of the transported cold envelope -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetTimeRegularity

def positiveFoot (σ α γ s : ℝ) (p : ℝ × ℝ) : ℝ :=
  AxialFlow.foot σ α γ s (max p.1 0) p.2

theorem positiveFoot_distance {α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (σ : ℝ) (p q : ℝ × ℝ) :
    |positiveFoot σ α γ s p - positiveFoot σ α γ s q| ≤
      |max p.1 0 - max q.1 0| * (|σ| + α) + |p.2 - q.2| := by
  have htime := AxialTransport.flightFoot_distance (σ := σ) hα hγ hs (le_max_right q.1 0)
    p.2 0 (max p.1 0)
  simp only [AxialTransport.flightFoot, mul_zero, add_zero, abs_zero, zero_add] at htime
  have hspace := AxialFlow.foot_lipschitz (σ := σ) (z := p.2) (w := q.2)
    hα hγ hs (le_max_right q.1 0)
  exact (abs_sub_le _ _ _).trans (add_le_add htime hspace)

theorem continuous_positiveFoot {α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (σ : ℝ) : Continuous (positiveFoot σ α γ s) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  have hc : Continuous (fun p : ℝ × ℝ =>
      |max p.1 0 - max q.1 0| * (|σ| + α) + |p.2 - q.2|) := by fun_prop
  apply squeeze_zero (fun p => abs_nonneg _)
    (fun p => positiveFoot_distance hα hγ hs σ p q)
  simpa only [sub_self, abs_zero, zero_mul, add_zero] using (hc.continuousAt (x := q)).tendsto

def positiveU (η K α γ s d : ℝ) (a : Bool) (p : ℝ × JetPrototype.Phase) : ℝ :=
  JetFreeTransport.free η K α γ s d p.1 a p.2 +
    JetSupersolution.epsilon K s d * JetBarrier.barrier η K α γ s d (max p.1 0) a p.2

theorem positiveU_eq {t : ℝ} (ht : 0 ≤ t) (η K α γ s d : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    positiveU η K α γ s d a (t, p) = JetSupersolution.U η K α γ s d t a p := by
  simp only [positiveU, JetSupersolution.U, max_eq_left ht]

theorem measurable_positiveU {α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (η K d : ℝ) (a : Bool) : Measurable (positiveU η K α γ s d a) := by
  have hfoot : Measurable (fun p : ℝ × JetPrototype.Phase =>
      AxialFlow.foot (sign a) α γ s (max p.1 0) p.2.1.2) :=
    (continuous_positiveFoot hα hγ hs (sign a)).measurable.comp
      (show Measurable (fun p : ℝ × JetPrototype.Phase => (p.1, p.2.1.2)) by fun_prop)
  have hvel : Measurable (fun p : ℝ × JetPrototype.Phase =>
      AxialFlow.velocity (sign a) α γ s (max p.1 0) p.2.1.2) := by
    have heq : (fun p : ℝ × JetPrototype.Phase =>
        AxialFlow.velocity (sign a) α γ s (max p.1 0) p.2.1.2) =
        (fun p => AxialFlow.profile (sign a) α γ s
          (AxialFlow.foot (sign a) α γ s (max p.1 0) p.2.1.2)) :=
      funext (fun _ => AxialFlow.velocity_spec hα)
    rw [heq]
    exact (AxialFlow.continuous_profile (sign a) α γ s).measurable.comp hfoot
  have hjoin : Measurable (fun p : ℝ × JetPrototype.Phase =>
      PlaneChart.join 0 (AxialFlow.velocity (sign a) α γ s (max p.1 0) p.2.1.2)) :=
    VelocityWeight.split.symm.measurable.comp (hvel.prodMk measurable_const)
  have hfree : Measurable (fun p : ℝ × JetPrototype.Phase =>
      JetFreeTransport.free η K α γ s d p.1 a p.2) := by
    apply (measurable_density η K α γ s d a).comp
    unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
    fun_prop
  have hbar : Measurable (fun p : ℝ × JetPrototype.Phase =>
      JetBarrier.barrier η K α γ s d (max p.1 0) a p.2) := by
    unfold JetBarrier.barrier JetBarrier.exponent JetBarrier.centerVelocity JetBarrier.distanceSquared
    fun_prop
  exact hfree.add (hbar.const_mul _)

end BoltzmannNonuniqueness.JetTimeRegularity

end

end

section

/-! # Monotonicity and the initial trace along free flights -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetBarrierTrace

theorem barrier_monotone {K α γ s d : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (η : ℝ) (label : Bool) (p : JetPrototype.Phase) :
    MonotoneOn (JetBarrierDerivative.along η K α γ s d label p) (Ioc 0 1) := by
  intro a ha b hb hab
  have hac := JetBarrierRegularity.barrier_ac hα hγ hs ha.1 hab η K d label p
  have hi : 0 ≤ ∫ t in a..b, deriv (JetBarrierDerivative.along η K α γ s d label p) t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    filter_upwards [ae_restrict_of_ae (JetBarrierDerivative.ae_barrier_derivative hK hα hγ hs hd η label p),
      ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hder := (ht (ha.1.trans_le hmem.1) (hmem.2.trans (hb.2.trans (by norm_num)))).2
    have hn : 0 ≤ (1 + (7 / 8 : ℝ) * ‖JetCoreFlight.error α γ s t label p‖ ^ 2 / d ^ 2) *
        JetBarrierDerivative.along η K α γ s d label p t := by
      apply mul_nonneg (by positivity)
      exact JetBarrier.barrier_nonneg hK hs.le hd.le η α γ t label _
    exact hn.trans hder
  rw [hac.integral_deriv_eq_sub] at hi
  linarith

theorem barrier_right_limit {K α γ s d : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (η : ℝ) (label : Bool) (p : JetPrototype.Phase) :
    ∃ l : ℝ, 0 ≤ l ∧ Tendsto (JetBarrierDerivative.along η K α γ s d label p)
      (𝓝[>] 0) (𝓝 l) := by
  let f := JetBarrierDerivative.along η K α γ s d label p
  have hmono : MonotoneOn f (Ioo 0 1) :=
    (barrier_monotone hK hα hγ hs hd η label p).mono Ioo_subset_Ioc_self
  have hb : BddBelow (f '' Ioo 0 1) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, _, rfl⟩
    exact JetBarrier.barrier_nonneg hK hs.le hd.le η α γ t label _
  have ht := hmono.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr zero_lt_one) hb
  refine ⟨_, ?_, ht⟩
  apply ge_of_tendsto ht
  filter_upwards [] with t
  exact JetBarrier.barrier_nonneg hK hs.le hd.le η α γ t label _

/-- A finite initial trace exists and dominates the initial color.
An explicit formula for the trace on spatial boundaries is unnecessary. -/
theorem supersolution_right_limit {K α γ s d : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (η : ℝ) (label : Bool) (p : JetPrototype.Phase) :
    ∃ l : ℝ, density η K α γ s d label p ≤ l ∧
      Tendsto (JetSupersolution.along η K α γ s d label p) (𝓝[>] 0) (𝓝 l) := by
  obtain ⟨l, hl, ht⟩ := barrier_right_limit hK hα hγ hs hd η label p
  refine ⟨density η K α γ s d label p + JetSupersolution.epsilon K s d * l, ?_, ?_⟩
  · exact le_add_of_nonneg_right (mul_nonneg (JetSupersolution.epsilon_nonneg hK hs hd) hl)
  · have hc : Tendsto (fun _ : ℝ => density η K α γ s d label p) (𝓝[>] 0)
        (𝓝 (density η K α γ s d label p)) := tendsto_const_nhds
    have h := hc.add (ht.const_mul (JetSupersolution.epsilon K s d))
    convert h using 1
    funext t
    exact JetSupersolution.along_eq η K α γ s d label p t

theorem supersolution_ac {α γ s a b : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ha : 0 < a) (hab : a ≤ b) (η K d : ℝ) (label : Bool) (p : JetPrototype.Phase) :
    AbsolutelyContinuousOnInterval (JetSupersolution.along η K α γ s d label p) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => density η K α γ s d label p) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hm := (JetBarrierRegularity.barrier_ac hα hγ hs ha hab η K d label p).const_mul
    (JetSupersolution.epsilon K s d)
  convert hc.add hm using 1
  funext t
  exact JetSupersolution.along_eq η K α γ s d label p t

end BoltzmannNonuniqueness.JetBarrierTrace

end

end

section

/-! # Gaussian parameter laws for the actual axial core map -/

noncomputable section

open MeasureTheory
open scoped NNReal
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetAxialLaw

theorem axialMap_abs_le {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d)
    (σ γ s t z w : ℝ) : |axialMap σ α γ s d t z w| ≤ (|σ| + α) + d * |w| := by
  have hv := AxialTransport.velocity_abs_le (σ := σ) (γ := γ) (s := s)
    (t := t) (z := z - t * d * w) hα
  have h := abs_add_le (d * w) (velocity σ α γ s t (z - t * d * w))
  rw [abs_mul, abs_of_nonneg hd] at h
  unfold axialMap
  linarith

def law (σ α γ s d t z : ℝ) : Measure ℝ :=
  GaussianSheets.axialLaw (1 / 2) (axialMap σ α γ s d t z)

theorem probability (σ α γ s d t z : ℝ) : IsProbabilityMeasure (law σ α γ s d t z) := by
  unfold law
  infer_instance

theorem moment {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 ≤ t) (σ z : ℝ) :
    SheetMeasures.AxialMoment (law σ α γ s d t z)
      (2 * Real.exp (16 * (|σ| + α) ^ 2)) := by
  have hm : Measurable (axialMap σ α γ s d t z) :=
    (axialHomeomorph hα hγ hs ht hd.ne' σ z).continuous.measurable
  have hb := axialMap_abs_le hα hd.le σ γ s t z
  exact ⟨GaussianSheets.integrable_axialLaw_exp (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)
      (by norm_num) (by positivity) hd.le hdmax hm hb,
    GaussianSheets.integral_axialLaw_exp_le (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)
      (by norm_num) (by positivity) hd.le hdmax hm hb⟩

end BoltzmannNonuniqueness.JetAxialLaw

end

end

section

/-! # Gaussian product domination in the actual core coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreMeasure

namespace BoltzmannNonuniqueness.JetGaussianProduct

def density (w : Transverse × ℝ) : ℝ :=
  gaussianDensity 1 w.1 * gaussianPDFReal 0 (1 / 2) w.2

def coefficient : ℝ := JetThermalKernel.bound * Real.exp 1 * (Real.pi * Real.sqrt Real.pi)

theorem density_eq (w : Transverse × ℝ) :
    density w = (Real.pi * Real.sqrt Real.pi)⁻¹ * Real.exp (-‖SheetMeasures.join w‖ ^ 2) := by
  unfold density
  rw [GaussianSheets.original_gaussian_density]
  simp only [gaussianDensity, one_pow, mul_one, div_one]
  rw [SheetMeasures.norm_join_sq]
  rw [show -(‖w.1‖ ^ 2 + w.2 ^ 2) = -‖w.1‖ ^ 2 + -w.2 ^ 2 by ring, Real.exp_add]
  field_simp

theorem density_nonneg (w : Transverse × ℝ) : 0 ≤ density w := by
  rw [density_eq]
  positivity

theorem kernel_bound (w : Transverse × ℝ) :
    JetThermalKernel.J (SheetMeasures.join w) ≤ coefficient * density w := by
  have hC : 0 ≤ coefficient := by
    unfold coefficient
    have := JetThermalKernel.bound_pos
    positivity
  by_cases hw : 1 ≤ ‖SheetMeasures.join w‖
  · rw [JetThermalKernel.J_zero hw]
    exact mul_nonneg hC (density_nonneg w)
  · have hnorm : ‖SheetMeasures.join w‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (SheetMeasures.join w)]
    have he : 1 ≤ Real.exp (1 - ‖SheetMeasures.join w‖ ^ 2) :=
      Real.one_le_exp_iff.mpr (by linarith)
    calc
      _ ≤ JetThermalKernel.bound := JetThermalKernel.J_le _
      _ ≤ JetThermalKernel.bound * Real.exp (1 - ‖SheetMeasures.join w‖ ^ 2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he JetThermalKernel.bound_pos.le
      _ = coefficient * density w := by
        rw [density_eq, sub_eq_add_neg, Real.exp_add]
        unfold coefficient
        field_simp

theorem gaussian_scaling {d : ℝ} (hd : 0 < d) (w : Transverse) :
    d ^ 2 * gaussianDensity d (d • w) = gaussianDensity 1 w := by
  unfold gaussianDensity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
  have he : -(d * ‖w‖) ^ 2 / d ^ 2 = -‖w‖ ^ 2 := by field_simp
  rw [he]
  simp only [one_pow, mul_one, div_one]
  field_simp

theorem gaussianLaw_map_smul {d : ℝ} (hd : 0 < d) :
    (gaussianLaw 1).map (fun w => d • w) = gaussianLaw d := by
  have hm := transverse_measurePreserving hd
  have hf : Measurable (fun w => ENNReal.ofReal (gaussianDensity d w)) := by
    unfold gaussianDensity
    fun_prop
  have hfg : Measurable (fun w => ENNReal.ofReal (gaussianDensity d (d • w))) :=
    hf.comp hm.measurable
  have heq : gaussianLaw 1 =
      (ENNReal.ofReal (d ^ 2) • (volume : Measure Transverse)).withDensity
        (fun w => ENNReal.ofReal (gaussianDensity d (d • w))) := by
    rw [withDensity_smul_measure, ← withDensity_smul _ hfg]
    unfold gaussianLaw
    congr 1
    funext w
    change ENNReal.ofReal (gaussianDensity 1 w) = ENNReal.ofReal (d ^ 2) * _
    rw [← ENNReal.ofReal_mul (sq_nonneg d), gaussian_scaling hd]
  rw [heq]
  ext B hB
  rw [Measure.map_apply hm.measurable hB,
    withDensity_apply _ (hB.preimage hm.measurable), gaussianLaw, withDensity_apply _ hB,
    ← lintegral_indicator (hB.preimage hm.measurable), ← lintegral_indicator hB]
  convert hm.lintegral_comp (hf.indicator hB) using 1
  apply lintegral_congr
  intro w
  rfl

def parameterLaw : Measure (Transverse × ℝ) :=
  (gaussianLaw 1).prod (gaussianReal 0 (1 / 2))

theorem parameterLaw_density : parameterLaw =
    ((volume : Measure Transverse).prod volume).withDensity (fun w => ENNReal.ofReal (density w)) := by
  unfold parameterLaw gaussianLaw
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  rw [prod_withDensity (by unfold gaussianDensity; fun_prop) (measurable_gaussianPDF 0 (1 / 2))]
  congr 1
  funext w
  rw [density, ENNReal.ofReal_mul (gaussianDensity_nonneg _ _)]
  rfl

theorem parameterLaw_map {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) :
    parameterLaw.map (velocityMap σ α γ s d t z) =
      SheetMeasures.sheetLaw d (JetAxialLaw.law σ α γ s d t z) := by
  have hm : Measurable (axialMap σ α γ s d t z) := (axialHomeomorph hα hγ hs ht hd.ne' σ z).continuous.measurable
  let : IsProbabilityMeasure (gaussianLaw 1) := gaussianLaw_isProbabilityMeasure (by norm_num)
  unfold parameterLaw SheetMeasures.sheetLaw SheetMeasures.transverseLaw JetAxialLaw.law
    GaussianSheets.axialLaw
  rw [ite_eq_right hd.ne', ← gaussianLaw_map_smul hd, Measure.map_prod_map _ _ (by fun_prop) hm,
    Measure.map_map SheetMeasures.join.measurable (by fun_prop)]
  rfl

end BoltzmannNonuniqueness.JetGaussianProduct

end

end

end OAI
