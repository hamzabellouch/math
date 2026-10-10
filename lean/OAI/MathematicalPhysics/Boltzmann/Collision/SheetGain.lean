import OAI.MathematicalPhysics.Boltzmann.Collision.CarlemanOperator
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Collision.WeightAlgebra
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricSlice
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

section

/-!
# Exponential tilting of cold sheets

These are the transverse density domination and axial moment-tail estimates
used in the proof of the uniform sheet gain bound, Section 3.
-/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture

namespace BoltzmannNonuniqueness.SheetTails

theorem gaussian_tilt_identity {d : ℝ} (hd : 0 < d) (u : Transverse) :
    Real.exp (2 * ‖u‖ ^ 2) * gaussianDensity d u =
      4 * Real.exp (-(3 / (4 * d ^ 2) - 2) * ‖u‖ ^ 2) * gaussianDensity (2 * d) u := by
  have hc : (Real.pi * d ^ 2)⁻¹ = 4 * (Real.pi * (2 * d) ^ 2)⁻¹ := by
    field_simp
    ring
  unfold gaussianDensity
  rw [hc]
  have he : 2 * ‖u‖ ^ 2 + -‖u‖ ^ 2 / d ^ 2 =
      -(3 / (4 * d ^ 2) - 2) * ‖u‖ ^ 2 + -‖u‖ ^ 2 / (2 * d) ^ 2 := by
    field_simp
    ring
  calc
    _ = (4 * (Real.pi * (2 * d) ^ 2)⁻¹) *
        (Real.exp (2 * ‖u‖ ^ 2) * Real.exp (-‖u‖ ^ 2 / d ^ 2)) := by ring
    _ = (4 * (Real.pi * (2 * d) ^ 2)⁻¹) *
        (Real.exp (-(3 / (4 * d ^ 2) - 2) * ‖u‖ ^ 2) *
          Real.exp (-‖u‖ ^ 2 / (2 * d) ^ 2)) := by rw [← Real.exp_add, he, Real.exp_add]
    _ = _ := by ring

/-- The widened transverse Gaussian retains a fixed Gaussian decay factor. -/
theorem gaussian_tilt_le {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 8) (u : Transverse) :
    Real.exp (2 * ‖u‖ ^ 2) * gaussianDensity d u ≤
      4 * Real.exp (-46 * ‖u‖ ^ 2) * gaussianDensity (2 * d) u := by
  have hd₂ : d ^ 2 ≤ 1 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdmax) (by linarith : 0 ≤ 1 / 8 + d)]
  have hk : 46 ≤ 3 / (4 * d ^ 2) - 2 := by
    have h : 48 ≤ 3 / (4 * d ^ 2) :=
      (le_div_iff₀ (by positivity : 0 < 4 * d ^ 2)).mpr (by nlinarith)
    linarith
  rw [gaussian_tilt_identity hd u]
  apply mul_le_mul_of_nonneg_right _ (gaussianDensity_nonneg _ _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖u‖]

theorem gaussian_tilt_tail_le {d U : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 8)
    (hU : 0 ≤ U) (u : Transverse) (hu : U ≤ ‖u‖) :
    Real.exp (2 * ‖u‖ ^ 2) * gaussianDensity d u ≤
      (4 * Real.exp (-46 * U ^ 2)) * gaussianDensity (2 * d) u := by
  apply (gaussian_tilt_le hd hdmax u).trans
  apply mul_le_mul_of_nonneg_right _ (gaussianDensity_nonneg _ _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg u]

theorem integrable_axial_tilt {ρ : Measure ℝ}
    (hρ : Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) ρ) :
    Integrable (fun a : ℝ => Real.exp (2 * a ^ 2)) ρ := by
  apply hρ.mono' (by fun_prop)
  filter_upwards [] with a
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg a]

theorem integral_axial_tilt_le {ρ : Measure ℝ} {L : ℝ}
    (hρ : Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) ρ)
    (hL : (∫ a, Real.exp (8 * a ^ 2) ∂ρ) ≤ L) :
    (∫ a, Real.exp (2 * a ^ 2) ∂ρ) ≤ L := by
  apply le_trans (integral_mono (integrable_axial_tilt hρ) hρ _) hL
  intro a
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg a]

theorem integral_axial_tilt_tail_le {ρ : Measure ℝ} {L U : ℝ}
    (hρ : Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) ρ)
    (hL : (∫ a, Real.exp (8 * a ^ 2) ∂ρ) ≤ L) (hU : 0 ≤ U) :
    (∫ a in {a : ℝ | U < |a|}, Real.exp (2 * a ^ 2) ∂ρ) ≤
      Real.exp (-6 * U ^ 2) * L := by
  have hs : MeasurableSet {a : ℝ | U < |a|} := measurableSet_lt measurable_const measurable_abs
  calc
    _ ≤ ∫ a in {a : ℝ | U < |a|}, Real.exp (-6 * U ^ 2) * Real.exp (8 * a ^ 2) ∂ρ :=
      setIntegral_mono_on (integrable_axial_tilt hρ).integrableOn
        (hρ.const_mul _).integrableOn hs (fun a ha => axial_tilt_tail hU ha.le)
    _ = Real.exp (-6 * U ^ 2) * (∫ a in {a : ℝ | U < |a|}, Real.exp (8 * a ^ 2) ∂ρ) :=
      integral_const_mul _ _
    _ ≤ Real.exp (-6 * U ^ 2) * (∫ a, Real.exp (8 * a ^ 2) ∂ρ) :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hρ
        (Filter.Eventually.of_forall (fun a => (Real.exp_pos _).le))) (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hL (Real.exp_nonneg _)

end BoltzmannNonuniqueness.SheetTails

end

end

section

/-!
# Probability sheets and their exponential tilts

An elementary sheet is the coordinate pushforward of a centered transverse
Gaussian (or the atom at zero) and an arbitrary axial probability law. The axial
exponential-moment hypothesis is recorded explicitly. All domination statements
below are inequalities of measures, so they also apply to nonnegative kernels.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.SheetTails

namespace BoltzmannNonuniqueness.SheetMeasures

/-- Coordinates are ordered transverse, then axial. -/
def join : Transverse × ℝ ≃ᵐ Velocity :=
  (MeasurableEquiv.prodComm : Transverse × ℝ ≃ᵐ ℝ × Transverse).trans split.symm

theorem norm_join_sq (p : Transverse × ℝ) :
    ‖join p‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  have h := split.apply_symm_apply (p.2, p.1)
  have hj : join p = split.symm (p.2, p.1) := rfl
  have ht : transverse (join p) = p.1 := by
    rw [hj]
    simpa only [split_apply] using congrArg Prod.snd h
  have ha : axial (join p) = p.2 := by
    rw [hj]
    simpa only [split_apply] using congrArg Prod.fst h
  rw [norm_sq_split, ht, ha]

def transverseLaw (d : ℝ) : Measure Transverse :=
  if d = 0 then Measure.dirac 0 else gaussianLaw d

theorem transverseLaw_isProbabilityMeasure {d : ℝ} (hd : 0 ≤ d) :
    IsProbabilityMeasure (transverseLaw d) := by
  unfold transverseLaw
  split_ifs with hz
  · infer_instance
  · exact gaussianLaw_isProbabilityMeasure (lt_of_le_of_ne hd (Ne.symm hz))

def sheetLaw (d : ℝ) (ρ : Measure ℝ) : Measure Velocity :=
  (transverseLaw d |>.prod ρ).map join

theorem sheetLaw_isProbabilityMeasure {d : ℝ} (hd : 0 ≤ d)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] : IsProbabilityMeasure (sheetLaw d ρ) := by
  have := transverseLaw_isProbabilityMeasure hd
  unfold sheetLaw
  infer_instance

/-- The exact axial hypothesis used throughout the sheet estimates. -/
structure AxialMoment (ρ : Measure ℝ) (L : ℝ) : Prop where
  integrable : Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) ρ
  bound : (∫ a, Real.exp (8 * a ^ 2) ∂ρ) ≤ L

theorem AxialMoment.nonneg {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) : 0 ≤ L :=
  (integral_nonneg (fun _ => (Real.exp_pos _).le)).trans h.bound

def axialTilt (ρ : Measure ℝ) : Measure ℝ :=
  ρ.withDensity (fun a => ENNReal.ofReal (Real.exp (2 * a ^ 2)))

def transverseTilt (d : ℝ) : Measure Transverse :=
  (transverseLaw d).withDensity (fun p => ENNReal.ofReal (Real.exp (2 * ‖p‖ ^ 2)))

def tiltedSheet (d : ℝ) (ρ : Measure ℝ) : Measure Velocity :=
  (sheetLaw d ρ).withDensity (fun p => ENNReal.ofReal (Real.exp (2 * ‖p‖ ^ 2)))

theorem axialTilt_mass {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    axialTilt ρ univ = ENNReal.ofReal (∫ a, Real.exp (2 * a ^ 2) ∂ρ) := by
  rw [axialTilt, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_axial_tilt h.integrable)]
  exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)

theorem axialTilt_mass_le {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    axialTilt ρ univ ≤ ENNReal.ofReal L := by
  rw [axialTilt_mass h]
  exact ENNReal.ofReal_le_ofReal (integral_axial_tilt_le h.integrable h.bound)

theorem axialTilt_finite {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    IsFiniteMeasure (axialTilt ρ) :=
  ⟨(axialTilt_mass_le h).trans_lt ENNReal.ofReal_lt_top⟩

/-- Normalization is defined even for the zero measure, using a harmless atom. -/
def normalizeFinite (μ : Measure ℝ) (hμ : μ univ < ∞) : ProbabilityMeasure ℝ :=
  MeasureTheory.FiniteMeasure.normalize (⟨μ, ⟨hμ⟩⟩ : FiniteMeasure ℝ)

theorem mass_smul_normalizeFinite (μ : Measure ℝ) (hμ : μ univ < ∞) :
    μ univ • (normalizeFinite μ hμ : Measure ℝ) = μ := by
  let ν : FiniteMeasure ℝ := ⟨μ, ⟨hμ⟩⟩
  ext s hs
  have he := MeasureTheory.FiniteMeasure.self_eq_mass_mul_normalize ν s
  have he' := congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) he.symm
  have hm : (ν.mass : ℝ≥0∞) = μ univ := FiniteMeasure.ennreal_mass
  have hs' : (ν s : ℝ≥0∞) = μ s := FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν s
  have hn : (ν.normalize s : ℝ≥0∞) = (normalizeFinite μ hμ : Measure ℝ) s :=
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν.normalize s
  rw [ENNReal.coe_mul, hm, hs', hn] at he'
  simpa only [Measure.smul_apply, smul_eq_mul] using he'

def axialProbability (ρ : Measure ℝ) {L : ℝ} (h : AxialMoment ρ L) : ProbabilityMeasure ℝ :=
  normalizeFinite (axialTilt ρ) (axialTilt_finite h).measure_univ_lt_top

theorem axialTilt_eq_mass_smul {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    axialTilt ρ = axialTilt ρ univ • (axialProbability ρ h : Measure ℝ) :=
  (mass_smul_normalizeFinite _ _).symm

private theorem smul_measure_mono {α : Type*} [MeasurableSpace α]
    {c d : ℝ≥0∞} (hcd : c ≤ d) (μ : Measure α) : c • μ ≤ d • μ := by
  apply Measure.le_iff.mpr
  intro s _
  simpa only [Measure.smul_apply, smul_eq_mul] using mul_le_mul_left hcd (μ s)

theorem axialTilt_le_probability {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    axialTilt ρ ≤ ENNReal.ofReal L • (axialProbability ρ h : Measure ℝ) := by
  rw [axialTilt_eq_mass_smul h]
  exact smul_measure_mono (axialTilt_mass_le h) _

private theorem withDensity_map_join (μ : Measure (Transverse × ℝ))
    (w : Velocity → ℝ≥0∞) (hw : Measurable w) :
    (μ.map join).withDensity w = (μ.withDensity (fun p => w (join p))).map join := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hf,
    lintegral_map (hw.mul hf) join.measurable,
    lintegral_map hf join.measurable]
  change (∫⁻ p, w (join p) * f (join p) ∂μ) = _
  exact (lintegral_withDensity_eq_lintegral_mul μ
    (show Measurable (fun p => w (join p)) from hw.comp join.measurable)
    (show Measurable (fun p => f (join p)) from hf.comp join.measurable)).symm

theorem tiltedSheet_eq (d : ℝ) (ρ : Measure ℝ) [SFinite ρ] :
    tiltedSheet d ρ = ((transverseTilt d).prod (axialTilt ρ)).map join := by
  unfold tiltedSheet sheetLaw
  rw [withDensity_map_join _ _ (by fun_prop)]
  congr 1
  rw [transverseTilt, axialTilt, prod_withDensity (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  rw [norm_join_sq, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem transverseTilt_zero : transverseTilt 0 = Measure.dirac 0 := by
  simp [transverseTilt, transverseLaw, dirac_withDensity]

theorem transverseTilt_gaussian {d : ℝ} (hd : 0 < d) :
    transverseTilt d = volume.withDensity (fun p =>
      ENNReal.ofReal (Real.exp (2 * ‖p‖ ^ 2) * gaussianDensity d p)) := by
  simp only [transverseTilt, transverseLaw, ite_eq_right (c := d = 0) hd.ne', gaussianLaw]
  rw [← withDensity_mul _ (measurable_gaussianDensity d |>.ennreal_ofReal) (by fun_prop)]
  congr 1
  funext p
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

theorem transverseTilt_le {d : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) :
    transverseTilt d ≤ (4 : ℝ≥0∞) • transverseLaw (2 * d) := by
  obtain rfl | hdpos := hd.eq_or_lt
  · rw [transverseTilt_zero]
    simp only [mul_zero, transverseLaw, ite_true]
    calc
      Measure.dirac (0 : Transverse) = (1 : ℝ≥0∞) • Measure.dirac 0 := (one_smul _ _).symm
      _ ≤ (4 : ℝ≥0∞) • Measure.dirac 0 := smul_measure_mono (by norm_num) _
  · rw [transverseTilt_gaussian hdpos]
    have h2d : 2 * d ≠ 0 := by positivity
    simp only [transverseLaw, ite_eq_right (c := 2 * d = 0) h2d, gaussianLaw]
    rw [← withDensity_smul _ (measurable_gaussianDensity (2 * d) |>.ennreal_ofReal)]
    apply withDensity_mono
    filter_upwards [] with p
    change ENNReal.ofReal _ ≤ 4 * ENNReal.ofReal _
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    apply (gaussian_tilt_le hdpos hdmax p).trans
    apply mul_le_mul_of_nonneg_right _ (gaussianDensity_nonneg _ _)
    have he : Real.exp (-46 * ‖p‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
    linarith

theorem tiltedSheet_le {d : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (ρ : Measure ℝ) [SFinite ρ] :
    tiltedSheet d ρ ≤ (4 : ℝ≥0∞) •
      ((transverseLaw (2 * d)).prod (axialTilt ρ)).map join := by
  have : SFinite (axialTilt ρ) := by unfold axialTilt; infer_instance
  rw [tiltedSheet_eq]
  have hp := Measure.prod_mono (transverseTilt_le hd hdmax)
    (le_refl (axialTilt ρ))
  have hm := Measure.map_mono hp join.measurable
  simpa only [Measure.prod_smul_left,
    Measure.map_smul _ join.measurable.aemeasurable] using hm

theorem tiltedSheet_le_probability {d L : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (h : AxialMoment ρ L) :
    tiltedSheet d ρ ≤ ENNReal.ofReal (4 * L) •
      sheetLaw (2 * d) (axialProbability ρ h) := by
  apply (tiltedSheet_le hd hdmax ρ).trans
  rw [axialTilt_eq_mass_smul h, Measure.prod_smul_right,
    Measure.map_smul _ join.measurable.aemeasurable, smul_smul]
  apply smul_measure_mono
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  simpa using mul_le_mul_right (axialTilt_mass_le h) (4 : ℝ≥0∞)

theorem tiltedSheet_mass_le {d L : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (h : AxialMoment ρ L) :
    tiltedSheet d ρ univ ≤ ENNReal.ofReal (4 * L) := by
  have := sheetLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
    (axialProbability ρ h : Measure ℝ)
  simpa using (tiltedSheet_le_probability hd hdmax h) univ

def axialTail (ρ : Measure ℝ) (U : ℝ) : Measure ℝ :=
  (axialTilt ρ).restrict {a : ℝ | U < |a|}

theorem axialTail_mass_le {ρ : Measure ℝ} {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) :
    axialTail ρ U univ ≤ ENNReal.ofReal (Real.exp (-6 * U ^ 2) * L) := by
  have hs : MeasurableSet {a : ℝ | U < |a|} := measurableSet_lt measurable_const measurable_abs
  rw [axialTail, Measure.restrict_apply_univ, axialTilt, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_axial_tilt h.integrable).integrableOn]
  · exact ENNReal.ofReal_le_ofReal (integral_axial_tilt_tail_le h.integrable h.bound hU)
  · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)

theorem axialTail_finite {ρ : Measure ℝ} {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) : IsFiniteMeasure (axialTail ρ U) :=
  ⟨(axialTail_mass_le h hU).trans_lt ENNReal.ofReal_lt_top⟩

def axialTailProbability (ρ : Measure ℝ) {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) : ProbabilityMeasure ℝ :=
  normalizeFinite (axialTail ρ U) (axialTail_finite h hU).measure_univ_lt_top

theorem axialTail_eq_mass_smul {ρ : Measure ℝ} {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) :
    axialTail ρ U = axialTail ρ U univ • (axialTailProbability ρ h hU : Measure ℝ) :=
  (mass_smul_normalizeFinite _ _).symm

theorem axialTail_le_probability {ρ : Measure ℝ} {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) :
    axialTail ρ U ≤ ENNReal.ofReal (Real.exp (-6 * U ^ 2) * L) •
      (axialTailProbability ρ h hU : Measure ℝ) := by
  rw [axialTail_eq_mass_smul h hU]
  exact smul_measure_mono (axialTail_mass_le h hU) _

theorem transverseTilt_finite {d : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) :
    IsFiniteMeasure (transverseTilt d) := by
  have := transverseLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
  have := Measure.smul_finite (transverseLaw (2 * d)) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)
  exact isFiniteMeasure_of_le ((4 : ℝ≥0∞) • transverseLaw (2 * d))
    (transverseTilt_le hd hdmax)

theorem transverseTilt_tail_le {d U : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hU : 0 ≤ U) :
    (transverseTilt d).restrict {p : Transverse | U < ‖p‖} ≤
      ENNReal.ofReal (4 * Real.exp (-46 * U ^ 2)) • transverseLaw (2 * d) := by
  obtain rfl | hdpos := hd.eq_or_lt
  · rw [transverseTilt_zero]
    have hz : (Measure.dirac (0 : Transverse)).restrict {p : Transverse | U < ‖p‖} = 0 := by
      apply Measure.restrict_eq_zero.mpr
      simp only [Measure.dirac_apply, indicator_of_notMem (show (0 : Transverse) ∉ {p : Transverse | U < ‖p‖} by simpa using not_lt.mpr hU)]
    rw [hz]
    exact bot_le
  · rw [transverseTilt_gaussian hdpos]
    have hs : MeasurableSet {p : Transverse | U < ‖p‖} :=
      measurableSet_lt measurable_const measurable_norm
    rw [restrict_withDensity hs, ← withDensity_indicator hs]
    have h2d : 2 * d ≠ 0 := by positivity
    simp only [transverseLaw, ite_eq_right (c := 2 * d = 0) h2d, gaussianLaw]
    rw [← withDensity_smul _ (measurable_gaussianDensity (2 * d) |>.ennreal_ofReal)]
    apply withDensity_mono
    filter_upwards [] with p
    by_cases hp : U < ‖p‖
    · simp only [indicator_of_mem (show p ∈ {p : Transverse | U < ‖p‖} from hp),
        Pi.smul_apply, smul_eq_mul]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.exp (-46 * U ^ 2))]
      exact ENNReal.ofReal_le_ofReal (gaussian_tilt_tail_le hdpos hdmax hU p hp.le)
    · simp only [indicator_of_notMem (show p ∉ {p : Transverse | U < ‖p‖} from hp)]
      exact bot_le

private theorem product_tail_le (μ : Measure Transverse) (ν : Measure ℝ)
    [SFinite μ] [SFinite ν] {u : ℝ} (hu : 0 ≤ u) :
    (μ.prod ν).restrict {p : Transverse × ℝ | u < ‖join p‖} ≤
      (μ.restrict {p : Transverse | u / 2 < ‖p‖}).prod ν +
        μ.prod (ν.restrict {a : ℝ | u / 2 < |a|}) := by
  have hs : {p : Transverse × ℝ | u < ‖join p‖} ⊆
      ({p : Transverse | u / 2 < ‖p‖} ×ˢ univ) ∪
        (univ ×ˢ {a : ℝ | u / 2 < |a|}) := by
    intro p hp
    by_contra hn
    have hn₁ : ‖p.1‖ ≤ u / 2 := by simpa using (not_or.mp hn).1
    have hn₂ : |p.2| ≤ u / 2 := by simpa using (not_or.mp hn).2
    have hn₃ := norm_join_sq p
    have hn₄ := sq_abs p.2
    have hs₁ : ‖p.1‖ ^ 2 ≤ (u / 2) ^ 2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hn₁
    have hs₂ : |p.2| ^ 2 ≤ (u / 2) ^ 2 := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr hn₂
    have hs₃ : u ^ 2 < ‖join p‖ ^ 2 := sq_lt_sq₀ hu (norm_nonneg _) |>.mpr hp
    nlinarith
  apply (Measure.restrict_mono_set _ hs).trans
  apply (Measure.restrict_union_le _ _).trans
  rw [← Measure.restrict_prod_eq_prod_univ]
  have he : (μ.prod ν).restrict (univ ×ˢ {a : ℝ | u / 2 < |a|}) =
      μ.prod (ν.restrict {a : ℝ | u / 2 < |a|}) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [he]

/-- The common decay coefficient for the two probability sheets in the tail. -/
def tailCoefficient (L u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (4 * Real.exp (-(3 / 2) * u ^ 2) * L)

private theorem transverse_tail_coefficient_le {L u : ℝ} (hL : 0 ≤ L) :
    ENNReal.ofReal (4 * Real.exp (-46 * (u / 2) ^ 2)) * ENNReal.ofReal L ≤
      tailCoefficient L u := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.exp (-46 * (u / 2) ^ 2))]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ hL
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg u]

private theorem axial_tail_coefficient (L u : ℝ) :
    (4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-6 * (u / 2) ^ 2) * L) =
      tailCoefficient L u := by
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  unfold tailCoefficient
  apply congrArg ENNReal.ofReal
  rw [show -6 * (u / 2) ^ 2 = -(3 / 2) * u ^ 2 by ring]
  ring

/-- The exponentially tilted norm tail is dominated by two probability sheets.
The second axial law is the normalized tilted axial tail and may be an atom
when the tail vanishes. -/
theorem tiltedSheet_tail_le {d L u : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (h : AxialMoment ρ L) (hu : 0 ≤ u) :
    (tiltedSheet d ρ).restrict {p : Velocity | u < ‖p‖} ≤
      tailCoefficient L u •
        (sheetLaw (2 * d) (axialProbability ρ h) +
          sheetLaw (2 * d) (axialTailProbability ρ h (by positivity : 0 ≤ u / 2))) := by
  have := transverseTilt_finite hd hdmax
  have := axialTilt_finite h
  have := transverseLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
  have := axialTail_finite h (show 0 ≤ u / 2 by positivity)
  have ht : ((transverseTilt d).restrict {p : Transverse | u / 2 < ‖p‖}).prod (axialTilt ρ) ≤
      tailCoefficient L u • (transverseLaw (2 * d)).prod (axialProbability ρ h) := by
    apply (Measure.prod_mono (transverseTilt_tail_le hd hdmax (by positivity))
      (axialTilt_le_probability h)).trans
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    exact smul_measure_mono (transverse_tail_coefficient_le h.nonneg) _
  have ha : (transverseTilt d).prod (axialTail ρ (u / 2)) ≤
      tailCoefficient L u •
        (transverseLaw (2 * d)).prod (axialTailProbability ρ h (by positivity : 0 ≤ u / 2)) := by
    apply (Measure.prod_mono (transverseTilt_le hd hdmax)
      (axialTail_le_probability h (by positivity))).trans
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, axial_tail_coefficient]
  rw [tiltedSheet_eq, Measure.restrict_map join.measurable (measurableSet_lt measurable_const measurable_norm)]
  have hb := (product_tail_le (transverseTilt d) (axialTilt ρ) hu).trans (add_le_add ht ha)
  have hm := Measure.map_mono hb join.measurable
  simpa only [Measure.map_add _ _ join.measurable,
    Measure.map_smul _ join.measurable.aemeasurable, ← smul_add, sheetLaw,
    axialTail, preimage_ofPred_eq] using hm

end BoltzmannNonuniqueness.SheetMeasures

end

end

section

/-!
# Geometric and Gaussian bounds for the gain of an elementary sheet

The ball integrals below use the actual three-dimensional collision chart.
The sheet laws may have an atomic transverse component and arbitrary axial
probability laws. No gain bound is included among the hypotheses.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures

namespace BoltzmannNonuniqueness.SheetGain

def ballRegion (v : Velocity) (R : ℝ) : Set (Velocity × (ℝ × ℝ)) :=
  {y | ‖PlaneChart.chart v y.1 y.2.1 y.2.2 - v‖ ≤ R}

def weightRatio (q : ℝ) (v ξ : Velocity) : ℝ≥0∞ :=
  ENNReal.ofReal (W q ξ / W q v)

def ballChartFiber (q : ℝ) (v p : Velocity) (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹) *
    ∫⁻ z : ℝ, ∫⁻ s : ℝ,
      if ‖PlaneChart.chart v p z s - v‖ ≤ R then
        weightRatio q v (PlaneChart.chart v p z s) else 0

theorem normal_join (v : Velocity) (p : Transverse × ℝ) :
    PlaneChart.normal v (SheetMeasures.join p) = transverse v - p.1 := by
  change transverse (v - PlaneChart.join p.1 p.2) = _
  rw [PlaneChart.transverse_sub, PlaneChart.transverse_join]

theorem slope_join (v : Velocity) (p : Transverse × ℝ) :
    PlaneChart.slope v (SheetMeasures.join p) =
      (axial v - p.2) / ‖transverse v - p.1‖ := by
  unfold PlaneChart.slope
  rw [normal_join]
  change axial (v - PlaneChart.join p.1 p.2) / _ = _
  rw [PlaneChart.axial_sub, PlaneChart.axial_join]

theorem offset_join (v : Velocity) (p : Transverse × ℝ) :
    PlaneChart.offset v (SheetMeasures.join p) = sliceOffset (transverse v) p.1 := by
  unfold PlaneChart.offset sliceOffset
  rw [normal_join]

theorem W_eq_transverseWeight (q : ℝ) (v : Velocity) :
    W q v = transverseWeight q (transverse v) := rfl

theorem chart_weight_join (q : ℝ) (v : Velocity) (p : Transverse × ℝ) (z s : ℝ) :
    W q (PlaneChart.chart v (SheetMeasures.join p) z s) =
      TransverseLine.lineWeight q (direction (transverse v - p.1))
        (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) s := by
  unfold W singularity
  rw [PlaneChart.transverse_chart, normal_join, offset_join, slope_join]
  rfl

theorem chart_ball_join {R : ℝ} (hR : 0 ≤ R) (v : Velocity) (p : Transverse × ℝ)
    (z s : ℝ) :
    ‖PlaneChart.chart v (SheetMeasures.join p) z s - v‖ ≤ R ↔
      s ∈ ballLineRegion (direction (transverse v - p.1)) (transverse v)
        (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) z R := by
  rw [← sq_le_sq₀ (norm_nonneg _) hR, PlaneChart.chart_displacement_norm_sq,
    normal_join, offset_join, slope_join]
  rfl

/-- Clipping the axial chart coordinate loses only the null endpoint `-R`. -/
theorem full_ballLineMass_eq {R : ℝ} (hR : 0 ≤ R) (q : ℝ) (e v : Transverse)
    (A B : ℝ) :
    (∫⁻ z : ℝ, ∫⁻ s in ballLineRegion e v (A - B * z) z R,
      ENNReal.ofReal (TransverseLine.lineWeight q e (A - B * z) s)) =
        ballLineMass q e v A B R (-R) R := by
  unfold ballLineMass
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne (-R)] with z hz
  by_cases hm : z ∈ Ioc (-R) R
  · simp only [indicator_of_mem hm]
  · rw [indicator_of_notMem hm]
    have hout : z < -R ∨ R < z := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hm
      rcases hm with hm | hm
      · exact Or.inl (lt_of_le_of_ne hm hz)
      · exact Or.inr hm
    rw [ballLineRegion_eq_empty_of_outside hR hout, Measure.restrict_empty, lintegral_zero_measure]

theorem ballChartFiber_le_slice {R : ℝ} (hR : 0 ≤ R) (q : ℝ)
    (v : Velocity) (p : Transverse × ℝ) :
    ballChartFiber q v (SheetMeasures.join p) R ≤
      normalizedBallSlice q (transverse v) (axial v) p.1 p.2 R (-R) R := by
  classical
  by_cases hp : RegularTransverse (transverse v) p.1
  · have hweight : 0 < transverseWeight q (transverse v) := transverseWeight_pos q _
    have hcoef : ENNReal.ofReal (‖transverse v - p.1‖⁻¹) *
        ENNReal.ofReal ((transverseWeight q (transverse v))⁻¹) =
      ENNReal.ofReal (1 / (transverseWeight q (transverse v) * ‖transverse v - p.1‖)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [one_div, mul_inv_rev]
    have hpoint : ∀ z s : ℝ,
        (if ‖PlaneChart.chart v (SheetMeasures.join p) z s - v‖ ≤ R then
          weightRatio q v (PlaneChart.chart v (SheetMeasures.join p) z s) else 0) =
        ENNReal.ofReal ((transverseWeight q (transverse v))⁻¹) *
          (ballLineRegion (direction (transverse v - p.1)) (transverse v)
            (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) z R).indicator
          (fun s => ENNReal.ofReal (TransverseLine.lineWeight q (direction (transverse v - p.1))
            (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) s)) s := by
      intro z s
      by_cases hm : s ∈ ballLineRegion (direction (transverse v - p.1)) (transverse v)
          (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) z R
      · have hc := (chart_ball_join hR v p z s).mpr hm
        rw [ite_eq_left hc, indicator_of_mem hm]
        unfold weightRatio
        rw [chart_weight_join, W_eq_transverseWeight, div_eq_mul_inv, mul_comm,
          ENNReal.ofReal_mul (inv_nonneg.mpr hweight.le)]
      · have hc := mt (chart_ball_join hR v p z s).mp hm
        simp only [ite_eq_right hc, indicator_of_notMem hm, mul_zero]
    have hm : ∀ z : ℝ, MeasurableSet (ballLineRegion (direction (transverse v - p.1))
        (transverse v) (sliceOffset (transverse v) p.1 -
          (axial v - p.2) / ‖transverse v - p.1‖ * z) z R) := by
      intro z
      unfold ballLineRegion TransverseLine.line
      apply measurableSet_le <;> fun_prop
    unfold ballChartFiber
    simp_rw [normal_join, hpoint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator (hm _)]
    rw [← mul_assoc, hcoef, full_ballLineMass_eq hR]
    rw [normalizedBallSlice, ite_eq_left hp]
  · rw [normalizedBallSlice, ite_eq_right hp]
    exact le_top

theorem weight_ball_sheet_bound {q d R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hR : 1 ≤ R) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    chartRegionGain (sheetLaw d ρ) (weightRatio q v) v (ballRegion v R) ≤
      2 * ENNReal.ofReal (geometricTotalConstant q * R ^ 2) := by
  have hs : (∫⁻ p, normalizedBallSlice q (transverse v) (axial v) p.1 p.2 R (-R) R
      ∂(transverseLaw d).prod ρ) ≤ ENNReal.ofReal (geometricTotalConstant q * R ^ 2) := by
    apply geometric_total_of_kernel_bound hq₁ hq₂ hR hv
    · obtain rfl | hdpos := hd.eq_or_lt
      · simpa only [transverseLaw, ite_true] using ae_regularTransverse_atom hv
      · simpa only [transverseLaw, ite_eq_right hdpos.ne'] using ae_regularTransverse_gaussian hv d
    · obtain rfl | hdpos := hd.eq_or_lt
      · simpa only [transverseLaw, ite_true] using atom_extendedKernel_lintegral_le q hv
      · simpa only [transverseLaw, ite_eq_right hdpos.ne'] using
          gaussian_extendedKernel_lintegral_le hq₁ hq₂ hdpos hv
  unfold chartRegionGain
  change 2 * (∫⁻ p, ballChartFiber q v p R ∂sheetLaw d ρ) ≤ _
  unfold sheetLaw
  rw [lintegral_map_equiv]
  exact mul_le_mul_right ((lintegral_mono (ballChartFiber_le_slice (by linarith) q v)).trans hs) 2

end BoltzmannNonuniqueness.SheetGain

end

end

end OAI
