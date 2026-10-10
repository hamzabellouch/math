import OAI.MathematicalPhysics.Boltzmann.Admissibility
import OAI.MathematicalPhysics.Boltzmann.Approximation.RegularizedCollisionDifference
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Collision.ScalarEntropyConvex
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteDepthKernelOrder
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

section

/-! # The integrable entropy error caused by positive regularization -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def entropyErrorCoefficient (q A b : ℝ) : ℝ :=
  tiltConstant*(2*A+tiltConstant)*
    (HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)

theorem entropyErrorCoefficient_nonneg {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (q : ℝ) :
    0 ≤ entropyErrorCoefficient q A b := by
  unfold entropyErrorCoefficient
  exact mul_nonneg (mul_nonneg tiltConstant_pos.le (by linarith [tiltConstant_pos]))
    (add_nonneg (HotApplication.realBound_pos q).le (CutoffLipschitz.frequencyConstant_nonneg hb q))

theorem cutoffCollision_measurable {f : Velocity → ℝ} (hfm : Measurable f) (b : ℝ) :
    Measurable (CutoffLipschitz.collision b f) := by
  let F : Unit × Velocity → ℝ := fun z => f z.2
  have hF : Measurable F := hfm.comp measurable_snd
  have hg := KineticCollisionNullSets.measurable_gain hF b
  have hν := KineticCollisionNullSets.measurable_frequency hF b
  have hs := (hg.sub (hF.mul hν)).comp
    (measurable_const.prodMk measurable_id : Measurable (fun v : Velocity => ((),v)))
  convert hs using 1
  funext v
  rfl


theorem entropy_regularization_error (hcarleman : Published.GPV2009CarlemanInput)
    {δ A q b p : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hA : 0 ≤ A)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hp : 1 < p)
    (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ v, 0 ≤ f v)
    (hfb : ∀ v, f v ≤ A*H q v) :
    Integrable (fun v => Real.log (gaussianRegularization δ f v/maxwellian v)*
      (CutoffLipschitz.collision b (gaussianRegularization δ f) v-CutoffLipschitz.collision b f v)) ∧
    |∫ v, Real.log (gaussianRegularization δ f v/maxwellian v)*
      (CutoffLipschitz.collision b (gaussianRegularization δ f) v-CutoffLipschitz.collision b f v)| ≤
      δ*entropyErrorCoefficient q A b*∫ v, logarithmicMajorant q (A+tiltConstant) p δ v := by
  let L := fun v => Real.log (gaussianRegularization δ f v/maxwellian v)
  let Q := fun v => CutoffLipschitz.collision b (gaussianRegularization δ f) v-
    CutoffLipschitz.collision b f v
  have hgm := gaussianRegularization_measurable δ hfm
  have hmm : Measurable maxwellian := by unfold maxwellian; fun_prop
  have hLm : Measurable L := (hgm.div hmm).log
  have hQm : Measurable Q := (cutoffCollision_measurable hgm b).sub (cutoffCollision_measurable hfm b)
  have hC := entropyErrorCoefficient_nonneg hA hb q
  have hδC : 0 ≤ δ*entropyErrorCoefficient q A b := mul_nonneg hδ.le hC
  have hmajor := (logarithmicMajorant_integrable (B := A+tiltConstant) (δ := δ) hq₂ hpi).const_mul
    (δ*entropyErrorCoefficient q A b)
  have hbound : ∀ᵐ v : Velocity, ‖L v*Q v‖ ≤
      δ*entropyErrorCoefficient q A b*logarithmicMajorant q (A+tiltConstant) p δ v := by
    filter_upwards [gaussianRegularization_collision_error hcarleman hδ.le hδone hA hq₁ hq₂ hb hfm hfn hfb]
      with v hv
    have hl : |L v| * H q v ≤ logarithmicMajorant q (A+tiltConstant) p δ v :=
      logarithm_weight_bound (add_nonneg hA tiltConstant_pos.le) hp hδ v
        (by dsimp [gaussianRegularization]; linarith [hfn v])
        (gaussianRegularization_bound hδ.le hδone hfb v)
    rw [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ |L v| * (δ*entropyErrorCoefficient q A b*H q v) :=
        mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = (δ*entropyErrorCoefficient q A b)*(|L v| * H q v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl hδC
  refine ⟨hmajor.mono' (hLm.mul hQm).aestronglyMeasurable hbound,?_⟩
  have h := norm_integral_le_of_norm_le hmajor hbound
  simpa only [Real.norm_eq_abs,integral_const_mul] using h

end BoltzmannNonuniqueness

end

end

section

/-! # Finite Gaussian relative entropy controls the required datum class -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

def entropyGaussian (v : Velocity) : ℝ :=
  maxwellian v * Real.exp ((1+‖v‖^2)/4)

theorem entropyGaussian_integrable : Integrable entropyGaussian := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (by norm_num : 0 < ((1/4:ℂ)).re) 0 (0:Velocity)).norm
  have hg : Integrable (fun v : Velocity => Real.exp (-‖v‖^2/4)) := by
    convert! h using 1
    funext v
    simp only [zero_mul,add_zero,Complex.norm_exp]
    congr 1
    norm_num
    norm_cast
    ring
  convert hg.const_mul ((2*Real.pi)^(-(3/2:ℝ))*Real.exp (1/4)) using 1
  funext v
  dsimp [entropyGaussian,maxwellian]
  simp only [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem entropy_controls_mass_energy {u : ℝ} (hu : 0 ≤ u) (v : Velocity) :
    (1+‖v‖^2)*u ≤ 4*(scalarRelativeEntropy (maxwellian v) u+entropyGaussian v) := by
  have h := entropyDual_le (maxwellian_pos v) hu ((1+‖v‖^2)/4)
  dsimp [entropyDual,entropyGaussian] at *
  nlinarith [maxwellian_pos v]

theorem finiteEntropy_of_relativeEntropy_integrable {f : Density}
    (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hH : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z))) :
    FiniteEntropyDatum f := by
  have hmajor : Integrable (fun z : Phase =>
      4*(scalarRelativeEntropy (maxwellian z.2) (f z)+entropyGaussian z.2)) :=
    (hH.add (entropyGaussian_integrable.comp_snd volume)).const_mul 4
  have hweight : Integrable (fun z : Phase => (1+‖z.2‖^2)*f z) := by
    apply hmajor.mono' ((measurable_const.add (measurable_snd.norm.pow_const 2)).mul hfm).aestronglyMeasurable
    filter_upwards [] with z
    change ‖(1+‖z.2‖^2)*f z‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hfn z))]
    exact entropy_controls_mass_energy (hfn z) z.2
  have hfi : Integrable f := by
    apply hweight.mono' hfm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (hfn z)]
    nlinarith [sq_nonneg ‖z.2‖,hfn z]
  have hEi : Integrable (fun z : Phase => ‖z.2‖^2*f z) := by
    apply hweight.mono' ((measurable_snd.norm.pow_const 2).mul hfm).aestronglyMeasurable
    filter_upwards [] with z
    change ‖‖z.2‖^2*f z‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hfn z))]
    nlinarith [hfn z]
  exact FiniteEntropyDatum.of_relativeEntropy_integrable (Filter.Eventually.of_forall hfn) hfi hEi hH

end BoltzmannNonuniqueness

end

end

section

/-! # The regularization error vanishes as the Gaussian is removed -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem tendsto_mul_abs_log_zero :
    Tendsto (fun δ : ℝ => δ*|Real.log δ|) (𝓝 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun δ : ℝ => |δ*Real.log δ|) (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_mul_log.abs.tendsto 0
  simpa only [norm_mul,Real.norm_eq_abs,abs_abs,abs_mul] using h

theorem tendsto_mul_affine_abs_log_zero (a b : ℝ) :
    Tendsto (fun δ : ℝ => δ*(a+b*|Real.log δ|)) (𝓝 0) (𝓝 0) := by
  have h := ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).mul_const a).add
    (tendsto_mul_abs_log_zero.mul_const b)
  convert h using 1
  · funext δ
    simp only [id_eq]
    ring
  · ring_nf

theorem integral_logarithmicMajorant {q B p δ : ℝ} (hq : q < 2)
    (hp : Integrable (fun v : Velocity => H q v^p)) :
    (∫ v, logarithmicMajorant q B p δ v) =
      (B^(p-1)/(p-1))*(∫ v, H q v^p)+
        (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|)*(∫ v, H q v)+
          (5/2:ℝ)*(∫ v, ‖v‖^2*H q v) := by
  have hH := (integrable_H hq).const_mul (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|)
  have hE : Integrable (fun v : Velocity => (5/2:ℝ)*(‖v‖^2*H q v)) := by
    simpa only [Nat.reduceMul] using (integrable_even_moment_H hq 1).const_mul (5/2:ℝ)
  have he : logarithmicMajorant q B p δ =
      (fun v => (B^(p-1)/(p-1))*H q v^p)+
        (fun v => (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|)*H q v)+
          (fun v => (5/2:ℝ)*(‖v‖^2*H q v)) := by
    funext v
    dsimp [logarithmicMajorant]
    ring
  rw [he,integral_add' ((hp.const_mul _).add hH) hE,integral_add' (hp.const_mul _) hH]
  simp only [integral_const_mul]

theorem tendsto_integrated_entropy_error {q B p : ℝ} (C : ℝ) (hq : q < 2)
    (hp : Integrable (fun v : Velocity => H q v^p)) :
    Tendsto (fun δ : ℝ => δ*C*(∫ v, logarithmicMajorant q B p δ v)) (𝓝 0) (𝓝 0) := by
  have h := (tendsto_mul_affine_abs_log_zero
    ((B^(p-1)/(p-1))*(∫ v, H q v^p)+
      |-(3/2:ℝ)*Real.log (2*Real.pi)| *(∫ v, H q v)+
      (5/2:ℝ)*(∫ v, ‖v‖^2*H q v)) (∫ v, H q v)).mul_const C
  convert h using 1
  · funext δ
    rw [integral_logarithmicMajorant hq hp]
    ring
  · ring_nf

end BoltzmannNonuniqueness

end

end

section

/-! # Passing an entropy-dissipation inequality through a vanishing error -/

noncomputable section

open Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem entropy_dissipation_of_vanishing_error {ι : Type*} {l : Filter ι} [NeBot l]
    {H H₀ error D : ι → ℝ} {h h₀ : ℝ} {d : ℝ≥0∞}
    (hh : Tendsto H l (𝓝 h)) (hh₀ : Tendsto H₀ l (𝓝 h₀))
    (herr : Tendsto error l (𝓝 0)) (hn : 0 ≤ h)
    (hDn : ∀ᶠ i in l, 0 ≤ D i)
    (hineq : ∀ᶠ i in l, H i-H₀ i+D i ≤ error i)
    (hfatou : d ≤ liminf (fun i => ENNReal.ofReal (D i)) l) :
    ENNReal.ofReal h+d ≤ ENNReal.ofReal h₀ := by
  have hHle : h ≤ h₀ := by
    have hlim : Tendsto (fun i => H₀ i+error i) l (𝓝 h₀) := by
      simpa only [add_zero] using hh₀.add herr
    apply le_of_tendsto_of_tendsto hh hlim
    filter_upwards [hDn,hineq] with i hi he
    linarith
  have hlim : Tendsto (fun i => H₀ i+error i-H i) l (𝓝 (h₀-h)) := by
    simpa only [add_zero] using (hh₀.add herr).sub hh
  have hmono : liminf (fun i => ENNReal.ofReal (D i)) l ≤
      liminf (fun i => ENNReal.ofReal (H₀ i+error i-H i)) l := by
    exact liminf_le_liminf (hineq.mono (fun i hi => ENNReal.ofReal_le_ofReal (by linarith)))
  rw [(ENNReal.tendsto_ofReal hlim).liminf_eq] at hmono
  calc
    _ ≤ ENNReal.ofReal h+ENNReal.ofReal (h₀-h) := add_le_add le_rfl (hfatou.trans hmono)
    _ = ENNReal.ofReal (h+(h₀-h)) := (ENNReal.ofReal_add hn (sub_nonneg.mpr hHle)).symm
    _ = _ := by congr 1; ring

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform integrability of the actual mass marginal from entropy -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem mass_marginal_uniformIntegrable {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => Compactness.fiberMass volume (f n)) 1 μ := by
  have hui := linearMoment_marginal_uniformIntegrable hfm hf hi hb
  have hbound n : ∀ᵐ x ∂μ, ‖Compactness.fiberMass volume (f n) x‖ₑ ≤
      ‖∫ v, linearMoment (f n) (x,v)‖ₑ := by
    filter_upwards [(linearMoment_integrable (hfm n) (hf n) (hi n)).prod_right_ae] with x hx
    apply enorm_le_iff_norm_le.mpr
    dsimp only [Compactness.fiberMass]
    have hln (v : Velocity) : 0 ≤ linearMoment (f n) (x,v) :=
      mul_nonneg (by dsimp only [Prod.snd]; positivity) (hf n (x,v))
    have hL0 : 0 ≤ ∫ v, linearMoment (f n) (x,v) := integral_nonneg hln
    rw [Real.norm_of_nonneg (integral_nonneg (fun v => hf n (x,v))),Real.norm_of_nonneg hL0]
    apply integral_mono_of_nonneg (ae_of_all _ (fun v => hf n (x,v))) hx
    filter_upwards [] with v
    change f n (x,v) ≤ (1+‖v‖)*f n (x,v)
    nlinarith [norm_nonneg v,hf n (x,v)]
  obtain ⟨hu,D,hD⟩ := hui
  have hm n := (Compactness.fiberMass_measurable (ν := volume) (hfm n)).aestronglyMeasurable (μ := μ)
  exact ⟨hu.ae_mono hm hbound,D,fun n => (eLpNorm_mono_enorm_ae (hm n) (hbound n)).trans (hD n)⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A uniform absolute-entropy moment from the relative-entropy bound -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

def entropyMomentCoefficient : ℝ :=
  2+3*|1-(3/2:ℝ)*Real.log (2*Real.pi)|

theorem entropyMomentCoefficient_nonneg : 0 ≤ entropyMomentCoefficient := by
  unfold entropyMomentCoefficient
  positivity

theorem entropyMoment_control {f : Density} {z : Phase} (hu : 0 ≤ f z) :
    entropyMoment f z ≤
      (1+4*entropyMomentCoefficient)*scalarRelativeEntropy (maxwellian z.2) (f z)+
        4*entropyMomentCoefficient*entropyGaussian z.2+maxwellian z.2 := by
  let u := f z
  let c := 1-(3/2:ℝ)*Real.log (2*Real.pi)
  have hu' : 0 ≤ u := hu
  have hE : 0 ≤ ‖z.2‖^2*u := mul_nonneg (sq_nonneg _) hu'
  have hm := (maxwellian_pos z.2).le
  have hc : c*u ≤ |c| *u := mul_le_mul_of_nonneg_right (le_abs_self c) hu'
  have hc' : -(|c| *u) ≤ c*u := by
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right (neg_abs_le c) hu'
  have hcu : 0 ≤ |c| *u := mul_nonneg (abs_nonneg c) hu'
  have hH := scalarRelativeEntropy_nonneg (maxwellian_pos z.2) hu'
  have he : scalarRelativeEntropy (maxwellian z.2) u =
      u*Real.log u-c*u+(1/2:ℝ)*(‖z.2‖^2*u)+maxwellian z.2 := by
    dsimp [scalarRelativeEntropy,c]
    rw [log_maxwellian]
    ring
  have ha : |u*Real.log u| ≤ u*Real.log u+2*(|c| *u+(1/2:ℝ)*(‖z.2‖^2*u)+maxwellian z.2) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hpre : entropyMoment f z ≤ scalarRelativeEntropy (maxwellian z.2) u+
      entropyMomentCoefficient*((1+‖z.2‖^2)*u)+maxwellian z.2 := by
    have habs : u*|Real.log u| = |u*Real.log u| := by rw [abs_mul,abs_of_nonneg hu']
    change u*(1+‖z.2‖^2+|Real.log u|) ≤ _
    rw [mul_add,habs]
    change _ ≤ scalarRelativeEntropy (maxwellian z.2) u+(2+3*|c|)*((1+‖z.2‖^2)*u)+maxwellian z.2
    have hEc : 0 ≤ |c| *(‖z.2‖^2*u) := mul_nonneg (abs_nonneg c) hE
    nlinarith
  have hb := mul_le_mul_of_nonneg_left (entropy_controls_mass_energy hu' z.2)
    entropyMomentCoefficient_nonneg
  exact hpre.trans (by nlinarith)

theorem entropyMoment_integral_control {f : Density} (hf : FiniteEntropyDatum f) :
    (∫ z, entropyMoment f z) ≤
      (1+4*entropyMomentCoefficient)*relativeEntropy f+
        4*entropyMomentCoefficient*(∫ z : Phase, entropyGaussian z.2)+
          (∫ z : Phase, maxwellian z.2) := by
  have hH := hf.integrable_relativeEntropy.congr (Filter.Eventually.of_forall (fun z =>
    (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
  have hG : Integrable (fun z : Phase => entropyGaussian z.2) :=
    entropyGaussian_integrable.comp_snd volume
  have hi := ((hH.const_mul (1+4*entropyMomentCoefficient)).add
    (hG.const_mul (4*entropyMomentCoefficient))).add integrable_maxwellian_phase
  have hb := integral_mono_ae hf.2.2 hi (hf.1.mono (fun _ hu => entropyMoment_control hu))
  simp only [Pi.add_apply] at hb
  have hsum := integral_add ((hH.const_mul (1+4*entropyMomentCoefficient)).add
    (hG.const_mul (4*entropyMomentCoefficient))) integrable_maxwellian_phase
  have hsum' := integral_add (hH.const_mul (1+4*entropyMomentCoefficient))
    (hG.const_mul (4*entropyMomentCoefficient))
  simp only [Pi.add_apply] at hsum hsum'
  rw [hsum,hsum',integral_const_mul,integral_const_mul] at hb
  have he : (∫ z, scalarRelativeEntropy (maxwellian z.2) (f z)) = relativeEntropy f :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => scalarRelativeEntropy_eq (maxwellian_pos z.2) _))
  rwa [he] at hb

end BoltzmannNonuniqueness

end

end

section

/-! # Passing the sum of nonnegative entropy and dissipation to a subsequential limit -/

noncomputable section

open Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem ennreal_liminf_add_nat (u v : ℕ → ℝ≥0∞) :
    liminf u atTop+liminf v atTop ≤ liminf (fun n => u n+v n) atTop := by
  simp_rw [liminf_eq_iSup_iInf_of_nat]
  apply ENNReal.iSup_add_iSup_le
  intro N M
  apply le_iSup_of_le (max N M)
  apply le_iInf₂
  intro k hk
  exact add_le_add (iInf₂_le k ((le_max_left N M).trans hk))
    (iInf₂_le k ((le_max_right N M).trans hk))

theorem entropy_dissipation_of_liminfs {H D : ℕ → ℝ≥0∞} {C : ℕ → ℝ}
    {h d : ℝ≥0∞} {c : ℝ}
    (hh : h ≤ liminf H atTop) (hd : d ≤ liminf D atTop)
    (hC : Tendsto C atTop (𝓝 c))
    (hupper : ∀ᶠ n in atTop, H n+D n ≤ ENNReal.ofReal (C n)) :
    h+d ≤ ENNReal.ofReal c := by
  have hm := liminf_le_liminf hupper
  rw [(ENNReal.tendsto_ofReal hC).liminf_eq] at hm
  exact (add_le_add hh hd).trans ((ennreal_liminf_add_nat H D).trans hm)

end BoltzmannNonuniqueness

end

end

section

/-! # Retaining a common entropy and dissipation budget under time averaging -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem entropy_dissipation_average_limit {H : ℕ → X → ℝ≥0∞} {h : X → ℝ≥0∞}
    {D C : ℕ → ℝ≥0∞} {d c : ℝ≥0∞}
    (hHm : ∀ n, Measurable (H n))
    (hh : (∫⁻ x, h x ∂μ) ≤ liminf (fun n => ∫⁻ x, H n x ∂μ) atTop)
    (hd : d ≤ liminf D atTop) (hC : Tendsto C atTop (𝓝 c))
    (hu : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, H n x+D n ≤ C n) :
    (∫⁻ x, h x ∂μ)+μ Set.univ*d ≤ μ Set.univ*c := by
  have hm := ENNReal.le_liminf_mul (u := fun _ : ℕ => μ Set.univ) (v := D) (f := atTop)
  have hd' : μ Set.univ*d ≤ liminf (fun n => μ Set.univ*D n) atTop := by
    apply (mul_le_mul' le_rfl hd).trans
    simpa only [liminf_const,Pi.mul_def] using hm
  have hu' : ∀ᶠ n in atTop, (∫⁻ x, H n x ∂μ)+μ Set.univ*D n ≤ μ Set.univ*C n := by
    filter_upwards [hu] with n hn
    have h := lintegral_mono_ae hn
    rw [lintegral_add_left (hHm n),lintegral_const,lintegral_const] at h
    simpa only [mul_comm] using h
  have hlim : Tendsto (fun n => μ Set.univ*C n) atTop (𝓝 (μ Set.univ*c)) :=
    ENNReal.Tendsto.const_mul hC (Or.inr (measure_ne_top μ Set.univ))
  apply (add_le_add hh hd').trans
  apply (ennreal_liminf_add_nat _ _).trans
  have hb := liminf_le_liminf hu'
  rwa [hlim.liminf_eq] at hb

end BoltzmannNonuniqueness

end

end

end OAI
