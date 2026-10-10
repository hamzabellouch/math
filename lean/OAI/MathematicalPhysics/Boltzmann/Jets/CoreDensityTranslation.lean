import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainRank
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialBandMeasure
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic
import OAI.MathematicalPhysics.Boltzmann.Compactness.SelectedCoreSelection
import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreMismatch
import OAI.MathematicalPhysics.Boltzmann.Jets.JetCoreConvergence

namespace OAI

section

/-! # The exact free-core integral over three Euclidean thermal parameters -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

def thermalCoordinates (w : FiveGainMap.V) : Transverse × ℝ :=
  SheetMeasures.join.symm (WithLp.toLp 2 w)

def thermalWeight (η K α γ s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (w : FiveGainMap.V) : ℝ := weight η K α γ s d t a x (thermalCoordinates w)

def thermalPoint (α γ s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (w : FiveGainMap.V) : Velocity :=
  JetCoreMeasure.velocityMap (JetPrototype.sign a) α γ s d t x.2 (thermalCoordinates w)

theorem thermalCoordinates_measurePreserving :
    MeasurePreserving thermalCoordinates volume ((volume : Measure Transverse).prod volume) := by
  exact (MeasurePreserving.symm SheetMeasures.join HotRectangleDensity.join_measurePreserving).comp
    (PiLp.volume_preserving_toLp (Fin 3))

theorem thermalWeight_measurable {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K d : ℝ) (a : Bool) (x : JetPrototype.Space) :
    Measurable (thermalWeight η K α γ s d t a x) :=
  (weight_measurable hα hγ hs ht η K d a x).comp thermalCoordinates_measurePreserving.measurable

theorem thermalPoint_measurable {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t) (a : Bool) (x : JetPrototype.Space) :
    Measurable (thermalPoint α γ s d t a x) :=
  (JetCoreMeasure.velocity_measurePreserving hα hγ hs hd ht (JetPrototype.sign a) x.2).measurable.comp
    thermalCoordinates_measurePreserving.measurable

theorem core_thermal_integral {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) (x : JetPrototype.Space)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂volume.withDensity
      (fun p => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x,p)))) =
    ∫⁻ w : FiveGainMap.V, ENNReal.ofReal (thermalWeight η K α γ s d t a x w)*
      f (thermalPoint α γ s d t a x w) := by
  have hvm := (JetCoreMeasure.velocity_measurePreserving hα hγ hs hd ht
    (JetPrototype.sign a) x.2).measurable
  have hwm := (weight_measurable hα hγ hs ht η K d a x).ennreal_ofReal
  have hfm : Measurable (fun w => f (JetCoreMeasure.velocityMap
      (JetPrototype.sign a) α γ s d t x.2 w)) := hf.comp hvm
  rw [← measure_identity hα hγ hs hd ht η K a x,lintegral_map hf hvm,
    lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
  exact (thermalCoordinates_measurePreserving.lintegral_comp
    (hwm.mul hfm)).symm

theorem thermalCoordinates_apply (w : FiveGainMap.V) :
    thermalCoordinates w = (transverse (WithLp.toLp 2 w),axial (WithLp.toLp 2 w)) := by
  change MeasurableEquiv.prodComm.symm (split (WithLp.toLp 2 w)) = _
  rw [split_apply]
  rfl

theorem thermalPoint_eq_center (α γ s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (xv w : FiveGainMap.V) (hx : xv 2 = x.2) :
    thermalPoint α γ s d t a x w = WithLp.toLp 2
      (FiveGainMap.thermalCenter (JetPrototype.sign a) α γ s d t xv w) := by
  apply split.injective
  simp only [thermalPoint,JetCoreMeasure.velocityMap,thermalCoordinates_apply,split_apply,
    PlaneChart.transverse_join,PlaneChart.axial_join]
  apply Prod.ext
  · change JetCoreMap.axialMap _ _ _ _ _ _ x.2 (w 2) =
      JetCoreMap.axialMap _ _ _ _ _ _ (xv 2) (w 2)
    rw [hx]
  · apply (WithLp.ext_iff 2).mpr
    funext i
    fin_cases i <;> simp [transverse,FiveGainMap.thermalCenter]

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Uniform density and support bounds in the actual thermal parameters -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermalWeight_bound {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V) :
    thermalWeight η K α γ s d t a x w ≤
      ((K*max 1 (α*γ)⁻¹)/(s+t))*JetThermalKernel.bound := by
  apply (weight_bound hK hα hγ hs ht η d a x (thermalCoordinates w)).trans
  exact mul_le_mul_of_nonneg_left (JetThermalKernel.J_le _)
    (div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) (by positivity))

theorem thermalWeight_zero {η K α γ s d t : ℝ} (a : Bool) (x : JetPrototype.Space)
    {w : FiveGainMap.V} (hw : 1 ≤ ‖WithLp.toLp 2 w‖) :
    thermalWeight η K α γ s d t a x w = 0 := by
  have he : SheetMeasures.join (thermalCoordinates w) = WithLp.toLp 2 w :=
    SheetMeasures.join.apply_symm_apply _
  unfold thermalWeight weight
  rw [he,JetThermalKernel.J_zero hw,mul_zero]

theorem dilated_thermalWeight_bound {r K α γ s t : ℝ} (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V) :
    r*thermalWeight η K α γ (r*s) d (r*t) a (r • x) w ≤
      ((K*max 1 (α*γ)⁻¹)/(s+t))*JetThermalKernel.bound := by
  apply (mul_le_mul_of_nonneg_left
    (thermalWeight_bound hK hα hγ (mul_pos hr hs) (mul_nonneg hr.le ht) η d a (r • x) w)
    hr.le).trans_eq
  have hst : s+t ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hs ht)
  field_simp

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Joint measurable thermal parameters on nonnegative time

Clamping time at zero provides a globally measurable representative, equal to
the physical parametrization at every nonnegative collision time.
-/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreDensity

abbrev ThermalArguments := ℝ × (Space × FiveGainMap.V)

theorem clamped_sourceFoot_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (σ d : ℝ) :
    Measurable (fun p : ThermalArguments =>
      sourceFoot σ α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2)) := by
  have hc := (AxialFlow.clamped_foot_continuous (σ := σ) hα hγ hs).comp
    (show Continuous (fun p : ThermalArguments =>
      (p.1,p.2.1.2-max 0 p.1*d*(p.2.2 2))) by fun_prop)
  exact hc.measurable

theorem clamped_axialMap_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (σ d : ℝ) :
    Measurable (fun p : ThermalArguments =>
      axialMap σ α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2)) := by
  have hc := (AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ hs).comp
    (show Continuous (fun p : ThermalArguments =>
      (p.1,p.2.1.2-max 0 p.1*d*(p.2.2 2))) by fun_prop)
  change Measurable (fun p : ThermalArguments =>
    d*(p.2.2 2)+AxialFlow.velocity σ α γ s (max 0 p.1)
      (p.2.1.2-max 0 p.1*d*(p.2.2 2)))
  exact (by fun_prop : Measurable (fun p : ThermalArguments => d*(p.2.2 2))).add hc.measurable

theorem clamped_thermalPoint_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (d : ℝ) (a : Bool) :
    Measurable (fun p : ThermalArguments =>
      thermalPoint α γ s d (max 0 p.1) a p.2.1 p.2.2) := by
  have ha := clamped_axialMap_measurable hα hγ hs (sign a) d
  have ht : Measurable (fun p : ThermalArguments => d • transverse (WithLp.toLp 2 p.2.2)) :=
    by fun_prop
  have h := SheetMeasures.join.measurable.comp (ht.prodMk ha)
  simp only [thermalPoint,thermalCoordinates_apply,JetCoreMeasure.velocityMap]
  change Measurable (fun p : ThermalArguments =>
    SheetMeasures.join (d • transverse (WithLp.toLp 2 p.2.2),
      axialMap (sign a) α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2)))
  exact h

theorem clamped_thermalWeight_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (η K d : ℝ) (a : Bool) :
    Measurable (fun p : ThermalArguments =>
      thermalWeight η K α γ s d (max 0 p.1) a p.2.1 p.2.2) := by
  have hfoot := clamped_sourceFoot_measurable hα hγ hs (sign a) d
  have hm : Measurable (fun p : ThermalArguments =>
      (JetGeometry.mask η s a).indicator (fun _ => (1 : ℝ))
        (p.2.1.1-max 0 p.1 • (d • transverse (WithLp.toLp 2 p.2.2)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η s a)).comp (by fun_prop)
  have hS : Measurable (fun p : ThermalArguments =>
      JetAxialWeight.S (γ*sourceFoot (sign a) α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2)/s)) :=
    JetAxialWeight.continuous_S.measurable.comp ((hfoot.const_mul γ).div_const s)
  have hc : Measurable (fun p : ThermalArguments =>
      compressed K α γ s (max 0 p.1)
        (sourceFoot (sign a) α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2))) := by
    unfold compressed
    exact (hS.const_mul K).div (measurable_const.add
      ((((by fun_prop : Measurable (fun p : ThermalArguments => max 0 p.1)).mul_const α).mul_const γ).mul hS))
  have hcut : Measurable (fun p : ThermalArguments =>
      (Ioo (-(1/8 : ℝ)) (1/8)).indicator (fun _ => (1 : ℝ))
        (sourceFoot (sign a) α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2))) :=
    (measurable_const.indicator measurableSet_Ioo).comp hfoot
  have hj : Measurable (fun p : ThermalArguments => JetThermalKernel.J (WithLp.toLp 2 p.2.2)) :=
    JetThermalKernel.J_smooth.continuous.measurable.comp (by fun_prop)
  convert (hm.mul (hcut.mul hc)).mul hj using 1
  funext p
  have hjp : SheetMeasures.join (transverse (WithLp.toLp 2 p.2.2),
      axial (WithLp.toLp 2 p.2.2)) = WithLp.toLp 2 p.2.2 := by
    rw [← thermalCoordinates_apply]
    exact SheetMeasures.join.apply_symm_apply _
  simp only [thermalWeight,weight,thermalCoordinates_apply,hjp,Pi.mul_apply]
  change _ = _
  rw [← indicator_mul_left]
  simp only [one_mul]
  rfl

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # A fixed-cardinality exceptional list has uniformly small first-core mass -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

def slabAmplitude (K α γ a : ℝ) : ℝ :=
  (K*max 1 (α*γ)⁻¹)*JetGaussianProduct.coefficient/a

theorem slabAmplitude_nonneg {K a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (α γ : ℝ) :
    0 ≤ slabAmplitude K α γ a := by
  have := JetThermalKernel.bound_pos
  unfold slabAmplitude JetGaussianProduct.coefficient
  positivity

theorem amplitude_le_slab {K a s t : ℝ} (hK : 0 ≤ K) (ha : 0 < a)
    (hs : 0 < s) (ht : a ≤ t) (α γ : ℝ) :
    amplitude K α γ s t ≤ slabAmplitude K α γ a := by
  have hc : 0 ≤ (K*max 1 (α*γ)⁻¹)*JetGaussianProduct.coefficient := by
    have := JetThermalKernel.bound_pos
    unfold JetGaussianProduct.coefficient
    positivity
  calc
    _ = ((K*max 1 (α*γ)⁻¹)*JetGaussianProduct.coefficient)/(s+t) := by
      unfold amplitude
      ring
    _ ≤ _ := div_le_div_of_nonneg_left hc ha (by linarith)

/-- The radius is uniform in the interval centers, core scale, and thermal width. -/
theorem core_bands_small_of_card {K α γ q a ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hε : 0 < ε) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s d t : ℝ}, 0 < s → 0 < d → d ≤ 1/16 → a ≤ t →
      ∀ (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity) (S : Finset ℝ),
      S.card ≤ N →
      ChartKernel.offAxis (normalizedCoreKernel η K α γ s d q sign) ((t,x),v)
        (axial ⁻¹' bands S δ) ≤ ENNReal.ofReal ε := by
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  let T : ℝ := ((N : ℝ)+1)*(A+1)
  have hT : 0 < T := by dsimp [T]; positivity
  have he : 0 < ε/T := div_pos hε hT
  obtain ⟨δ,hδ,hband⟩ := core_axial_bands (α := α) hq₁ hq₂ he
  refine ⟨δ,hδ,?_⟩
  intro s d t hs hd hdmax ht η sign x v S hS
  by_cases hv : transverse v = 0
  · rw [ChartKernel.offAxis_axis _ _ hv]
    simp
  rw [ChartKernel.offAxis_apply _ _ hv]
  have hb := hband hK hα hγ hs hd hdmax (ha.le.trans ht) η sign x v hv S
  have hcard : (S.card : ℝ) ≤ N := by exact_mod_cast hS
  have hcoef : (S.card : ℝ)*amplitude K α γ s t ≤ T := by
    have hi := mul_le_mul hcard (amplitude_le_slab hK ha hs ht α γ)
      (amplitude_nonneg hK hs (ha.le.trans ht) α γ) (Nat.cast_nonneg N)
    dsimp only [A] at hA
    have hNA : (N : ℝ)*A ≤ T := by dsimp [T]; nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
    exact hi.trans hNA
  calc
    _ ≤ _ := hb
    _ = ENNReal.ofReal ((S.card : ℝ)*amplitude K α γ s t*(ε/T)) := by
      rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hs (ha.le.trans ht) α γ),
        ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (T*(ε/T)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoef he.le)
    _ = ENNReal.ofReal ε := by rw [mul_div_cancel₀ _ hT.ne']

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniform first-kernel transverse concentration on a positive time slab -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem core_away_small_of_transverse {K α γ q a b ε : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ {s d t : ℝ}, 0 < s → 0 < d → d ≤ 1/16 → a ≤ t →
      ∀ (η : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity),
      ‖transverse v‖ ≤ r →
      ChartKernel.offAxis (normalizedCoreKernel η K α γ s d q sign) ((t,x),v)
        {w | b ≤ ‖transverse w‖} ≤ ENNReal.ofReal ε := by
  let A := slabAmplitude K α γ a
  have hA : 0 ≤ A := slabAmplitude_nonneg hK ha α γ
  have he : 0 < ε/(A+1) := div_pos hε (by positivity)
  obtain ⟨r,hr,haway⟩ := core_axis_input (α := α) hq₁ hq₂ hb he
  refine ⟨r,hr,?_⟩
  intro s d t hs hd hdmax ht η sign x v hvr
  by_cases hv : transverse v = 0
  · rw [ChartKernel.offAxis_axis _ _ hv]
    simp
  rw [ChartKernel.offAxis_apply _ _ hv,inputKernel_region sign (t,x) v
    (show MeasurableSet {w : Velocity | b ≤ ‖transverse w‖} from
      measurableSet_le measurable_const ChartKernel.measurable_transverse.norm)]
  change ChartKernel.normalizedMeasure (coreKernel η K α γ s d sign (t,x)) q v
    (AxisInput.away v b) ≤ _
  apply (haway hK hα hγ hs hd hdmax (ha.le.trans ht) η sign x v hv hvr).trans
  rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hs (ha.le.trans ht) α γ)]
  apply ENNReal.ofReal_le_ofReal
  have hcoef := amplitude_le_slab hK ha hs ht α γ
  have hprod : (A+1)*(ε/(A+1)) = ε := by field_simp
  calc
    _ ≤ (A+1)*(ε/(A+1)) :=
      mul_le_mul_of_nonneg_right (hcoef.trans (by change A ≤ A+1; linarith)) he.le
    _ = _ := hprod

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Matching translated core densities with the physical dilation -/

noncomputable section

open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem spatialMap_dilated_translate {r : ℝ} (hr : r ≠ 0) (x : Velocity) (n : Lattice) :
    JetPeriodicDatum.spatialMap (r • (x-r⁻¹ • latticeVector n)) =
      JetPeriodicDatum.spatialMap (r • x)-displacement n := by
  rw [smul_sub,smul_smul,mul_inv_cancel₀ hr,one_smul]
  rfl

theorem copyCoreDensity_eq {r : ℝ} (hr : r ≠ 0) (s₀ η K α γ d₀ : ℝ)
    (i : Label) (z : KineticPhase) :
    copyCoreDensity r s₀ η K α γ d₀ i z = ENNReal.ofReal r*
      ENNReal.ofReal (JetFreeTransport.free η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) (r*z.1.1) i.positive
        (WeightedTranslation.shift (displacement i.lattice)
          (JetPeriodicDatum.spatialMap (r • z.1.2),z.2))) := by
  change ENNReal.ofReal r*ENNReal.ofReal
    (JetFreeTransport.free _ _ _ _ _ _ _ _
      (JetPeriodicDatum.spatialMap (r • (z.1.2-r⁻¹ • latticeVector i.lattice)),z.2)) = _
  rw [spatialMap_dilated_translate hr]
  rfl

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
