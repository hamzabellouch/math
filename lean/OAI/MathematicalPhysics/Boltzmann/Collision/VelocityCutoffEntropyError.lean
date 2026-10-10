import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed

namespace OAI

section

/-! # Uniform integrability of the linear velocity moment from entropy and energy -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def linearMoment (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ := (1+‖p.2‖)*f p

def velocityLinearCut (R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  if ‖p.2‖ ≤ R then linearMoment f p else 0

theorem linearMoment_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (linearMoment f) := (measurable_const.add measurable_snd.norm).mul hf

theorem velocityLinearCut_measurable (R : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (velocityLinearCut R f) := (linearMoment_measurable hf).ite
      (measurableSet_le measurable_snd.norm measurable_const) measurable_const

theorem linearMoment_integrable {μ : Measure (X × Velocity)} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) μ) :
    Integrable (linearMoment f) μ := by
  apply (hi.const_mul 2).mono' (linearMoment_measurable hfm).aestronglyMeasurable
  filter_upwards [] with p
  change ‖(1+‖p.2‖)*f p‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hf p))]
  have h : 1+‖p.2‖ ≤ 2*(1+‖p.2‖^2+|Real.log (f p)|) := by
    nlinarith [sq_nonneg (‖p.2‖-1),abs_nonneg (Real.log (f p))]
  simpa only [linearMoment,entropyGauge,mul_assoc,mul_left_comm,mul_comm] using
    mul_le_mul_of_nonneg_right h (hf p)

omit [MeasurableSpace X] in
theorem velocityLinearCut_error {R : ℝ} (hR : 0 < R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    |linearMoment f p-velocityLinearCut R f p| ≤ 2*entropyGauge f p/R := by
  by_cases hp : ‖p.2‖ ≤ R
  · simp only [velocityLinearCut,ite_eq_left hp,sub_self,abs_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (entropyGauge_nonneg hf p)) hR.le
  · have hr : R ≤ ‖p.2‖ := (lt_of_not_ge hp).le
    simp only [velocityLinearCut,ite_eq_right hp,sub_zero,linearMoment]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (hf p))]
    apply (le_div_iff₀ hR).mpr
    have hcoeff : (1+‖p.2‖)*R ≤ 2*(1+‖p.2‖^2+|Real.log (f p)|) := by
      have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1+‖p.2‖ by positivity)
      nlinarith [sq_nonneg (‖p.2‖-1),abs_nonneg (Real.log (f p))]
    simpa only [entropyGauge,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_right hcoeff (hf p)

theorem velocityLinearCut_integrable {μ : Measure (X × Velocity)} (R : ℝ)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) μ) : Integrable (velocityLinearCut R f) μ := by
  apply (linearMoment_integrable hfm hf hi).mono'
    (velocityLinearCut_measurable R hfm).aestronglyMeasurable
  filter_upwards [] with p
  have hn : 0 ≤ linearMoment f p := mul_nonneg (by positivity) (hf p)
  by_cases hp : ‖p.2‖ ≤ R
  · rw [velocityLinearCut,ite_eq_left hp,Real.norm_of_nonneg hn]
  · rw [velocityLinearCut,ite_eq_right hp,norm_zero]
    exact hn

theorem velocityLinearCut_L1_error {μ : Measure (X × Velocity)} {R C : ℝ} (hR : 0 < R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) μ) (hb : (∫ p, entropyGauge f p ∂μ) ≤ C) :
    eLpNorm (fun p => linearMoment f p-velocityLinearCut R f p) 1 μ ≤ ENNReal.ofReal (2*C/R) := by
  have he := (linearMoment_integrable hfm hf hi).sub (velocityLinearCut_integrable R hfm hf hi)
  change Integrable (fun p => linearMoment f p-velocityLinearCut R f p) μ at he
  rw [eLpNorm_one_eq_lintegral_enorm he.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm he]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ p, 2*entropyGauge f p/R ∂μ :=
      integral_mono he.norm ((hi.const_mul 2).div_const R) (fun p => by
        simpa only [Real.norm_eq_abs] using velocityLinearCut_error hR hf p)
    _ = 2*(∫ p, entropyGauge f p ∂μ)/R := by rw [integral_div,integral_const_mul]
    _ ≤ 2*C/R := div_le_div_of_nonneg_right (by linarith) hR.le

theorem linearMoment_uniformIntegrable {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X × Velocity → ℝ} {C : ℝ} (hfm : ∀ n, Measurable (f n))
    (hf : ∀ n p, 0 ≤ f n p) (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => linearMoment (f n)) 1 (μ.prod volume) := by
  have hui := uniformIntegrable_of_entropyGauge hfm hf hi hb
  apply Compactness.uniformIntegrable_of_approximation (g := fun j n => velocityLinearCut ((j:ℝ)+1) (f n))
  · intro j
    let a : X × Velocity → ℝ := fun p => if ‖p.2‖ ≤ (j:ℝ)+1 then 1+‖p.2‖ else 0
    have ha : Measurable a := (measurable_const.add measurable_snd.norm).ite
      (measurableSet_le measurable_snd.norm measurable_const) measurable_const
    let D : ℝ≥0 := ⟨(j:ℝ)+2,by positivity⟩
    have hD (p : X × Velocity) : |a p| ≤ D := by
      change |if ‖p.2‖ ≤ (j:ℝ)+1 then 1+‖p.2‖ else 0| ≤ (j:ℝ)+2
      split_ifs with hp
      · rw [abs_of_nonneg (by positivity)]
        linarith
      · simp only [abs_zero]
        positivity
    change UniformIntegrable (fun n p => if ‖p.2‖ ≤ (j:ℝ)+1 then
      (1+‖p.2‖)*f n p else 0) 1 (μ.prod volume)
    simpa only [a,ite_mul,zero_mul] using
      Compactness.uniformIntegrable_of_bounded_multiplier hui ha D hD
  · intro ε hε
    obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (2*C) hε
    exact ⟨j,fun n => (velocityLinearCut_L1_error (by positivity) (hfm n) (hf n) (hi n) (hb n)).trans hj⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Compactly supported unit-mass velocity kernels of arbitrarily small radius -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem exists_velocity_mollifier {δ : ℝ} (hδ : 0 < δ) :
    ∃ χ : C(Velocity,ℝ), HasCompactSupport χ ∧ Integrable χ ∧
      (∀ a, 0 ≤ χ a) ∧ (∫ a, χ a) = 1 ∧ (∀ a, χ a ≠ 0 → ‖a‖ < δ) := by
  let b : ContDiffBump (0 : Velocity) := ⟨δ/2,δ,by linarith,by linarith⟩
  let χ : C(Velocity,ℝ) := ⟨b.normed volume,b.continuous_normed⟩
  refine ⟨χ,b.hasCompactSupport_normed,b.integrable_normed,?_,b.integral_normed,?_⟩
  · exact b.nonneg_normed
  · intro a ha
    have hs : a ∈ Function.support (b.normed (volume : Measure Velocity)) := ha
    rw [b.support_normed_eq] at hs
    simpa only [Metric.mem_ball,dist_zero_right] using hs

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Uniform integrability of the spatial mass and first-moment marginal -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem linearMoment_marginal_uniformIntegrable {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X × Velocity → ℝ} {C : ℝ} (hfm : ∀ n, Measurable (f n))
    (hf : ∀ n p, 0 ≤ f n p) (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n x => ∫ v, linearMoment (f n) (x,v)) 1 μ := by
  have hui := linearMoment_uniformIntegrable hfm hf hi hb
  have he (R : ℝ) (n : ℕ) (x : X) :
      (∫ v, velocityLinearCut R (f n) (x,v)) =
        ∫ v in Metric.closedBall (0:Velocity) R, linearMoment (f n) (x,v) := by
    rw [← integral_indicator Metric.isClosed_closedBall.measurableSet]
    congr 1
    ext v
    simp only [velocityLinearCut,indicator,Metric.mem_closedBall,dist_zero_right]
  apply Compactness.uniformIntegrable_of_approximation
    (g := fun j n x => ∫ v, velocityLinearCut ((j:ℝ)+1) (f n) (x,v))
  · intro j
    let s : Set Velocity := Metric.closedBall 0 ((j:ℝ)+1)
    let : IsFiniteMeasure ((volume : Measure Velocity).restrict s) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) ((j:ℝ)+1)).measure_lt_top.ne
    have hu := Compactness.uniformIntegrable_restrict hui (univ ×ˢ s)
    rw [← Measure.prod_restrict,Measure.restrict_univ] at hu
    have hm := Compactness.uniformIntegrable_integral (fun n => linearMoment_measurable (hfm n)) hu
    simpa only [he] using hm
  · intro ε hε
    obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (2*C) hε
    refine ⟨j,fun n => ?_⟩
    have hfi := linearMoment_integrable (hfm n) (hf n) (hi n)
    have hgi := velocityLinearCut_integrable ((j:ℝ)+1) (hfm n) (hf n) (hi n)
    have hae : (fun x => (∫ v, linearMoment (f n) (x,v))-
        ∫ v, velocityLinearCut ((j:ℝ)+1) (f n) (x,v)) =ᵐ[μ]
      (fun x => ∫ v, linearMoment (f n) (x,v)-velocityLinearCut ((j:ℝ)+1) (f n) (x,v)) := by
      filter_upwards [hfi.prod_right_ae,hgi.prod_right_ae] with x hfx hgx
      exact (integral_sub hfx hgx).symm
    rw [eLpNorm_congr_ae hae]
    exact (Compactness.eLpNorm_integral_le
      ((linearMoment_measurable (hfm n)).sub (velocityLinearCut_measurable ((j:ℝ)+1) (hfm n)))).trans
      ((velocityLinearCut_L1_error (by positivity) (hfm n) (hf n) (hi n) (hb n)).trans hj)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing bounded velocity cutoffs by the uniform energy-entropy budget -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem velocityCutoff_error_le {f : X × Velocity → ℝ} {β : Velocity → ℝ} {R : ℝ}
    (hR : 0 < R) (hf : ∀ p, 0 ≤ f p) (hβ0 : ∀ v, 0 ≤ β v) (hβ1 : ∀ v, β v ≤ 1)
    (hβeq : ∀ v, ‖v‖ ≤ R → β v = 1) (p : X × Velocity) :
    |f p-β p.2*f p| ≤ entropyGauge f p/R^2 := by
  have hfn := hf p
  have hnon : 0 ≤ f p-β p.2*f p := by nlinarith [hβ1 p.2]
  rw [abs_of_nonneg hnon]
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  by_cases hv : ‖p.2‖ ≤ R
  · rw [hβeq p.2 hv,one_mul,sub_self,zero_mul]
    exact entropyGauge_nonneg hf p
  · have hv' : R < ‖p.2‖ := lt_of_not_ge hv
    have hs : R^2 ≤ ‖p.2‖^2 := by nlinarith
    have hle : f p-β p.2*f p ≤ f p := by nlinarith [hβ0 p.2]
    have hlog := abs_nonneg (Real.log (f p))
    unfold entropyGauge
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg R),
      mul_le_mul_of_nonneg_left hs hfn,mul_nonneg hfn hlog]

theorem velocityCutoff_L1_bound {μ : Measure (X × Velocity)} {f : X × Velocity → ℝ}
    {β : Velocity → ℝ} {R C : ℝ} (hR : 0 < R)
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hβm : Measurable β)
    (hβ0 : ∀ v, 0 ≤ β v) (hβ1 : ∀ v, β v ≤ 1)
    (hβeq : ∀ v, ‖v‖ ≤ R → β v = 1)
    (hi : Integrable (entropyGauge f) μ) (hb : (∫ p, entropyGauge f p ∂μ) ≤ C) :
    eLpNorm (fun p => f p-β p.2*f p) 1 μ ≤ ENNReal.ofReal (C/R^2) := by
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hbi : Integrable (fun p => β p.2*f p) μ := hfi.bdd_mul
    (hβm.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun p => by rw [Real.norm_of_nonneg (hβ0 p.2)]; exact hβ1 p.2))
  have hei := hfi.sub hbi
  change Integrable (fun p => f p-β p.2*f p) μ at hei
  rw [eLpNorm_one_eq_lintegral_enorm hei.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hei]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ p, entropyGauge f p/R^2 ∂μ := integral_mono hei.norm (hi.div_const (R^2))
      (fun p => by simpa only [Real.norm_eq_abs] using velocityCutoff_error_le hR hf hβ0 hβ1 hβeq p)
    _ = (∫ p, entropyGauge f p ∂μ)/R^2 := integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right hb (sq_nonneg R)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
