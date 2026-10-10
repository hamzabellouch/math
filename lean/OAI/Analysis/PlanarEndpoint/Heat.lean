import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphTree

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
namespace PlanarEndpoint

lemma gaussianWeight_superlevel {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (_ht1 : t < 1) :
    {z : Plane | t < gaussianWeight a z} = ball 0 (Real.sqrt (-Real.log t / a)) := by
  ext z
  simp only [mem_ofPred_eq, mem_ball, dist_zero_right]
  rw [Real.lt_sqrt (norm_nonneg z), lt_div_iff₀ ha]
  unfold gaussianWeight
  rw [← Real.log_lt_iff_lt_exp ht]
  constructor <;> intro h <;> nlinarith

lemma gaussianWeight_superlevel_empty {a t : ℝ} (ha : 0 ≤ a) (ht : 1 ≤ t) :
    {z : Plane | t < gaussianWeight a z} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact (not_lt_of_ge (le_trans (gaussianWeight_le_one ha z) ht)) hz

lemma lintegral_gaussianWeight_le_of_ball (μ ν : Measure Plane) (C : ℝ≥0)
    (hball : ∀ r : ℝ, 0 < r → μ (ball 0 r) ≤ (C : ℝ≥0∞) * ν (ball 0 r))
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ z, ENNReal.ofReal (gaussianWeight a z) ∂μ ≤
      (C : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (gaussianWeight a z) ∂ν := by
  have hc : Continuous (gaussianWeight a) := by unfold gaussianWeight; fun_prop
  rw [lintegral_eq_lintegral_meas_lt μ
    (Eventually.of_forall fun z => (gaussianWeight_pos a z).le) hc.aemeasurable,
    lintegral_eq_lintegral_meas_lt ν
    (Eventually.of_forall fun z => (gaussianWeight_pos a z).le) hc.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases ht1 : t < 1
  · rw [gaussianWeight_superlevel ha ht ht1]
    apply hball
    apply Real.sqrt_pos.2
    exact div_pos (neg_pos.mpr (Real.log_neg ht ht1)) ha
  · rw [gaussianWeight_superlevel_empty ha.le (le_of_not_gt ht1)]
    simp

def heatKernel (a : ℝ) (z : Plane) : ℝ :=
  (4 * Real.pi * a)⁻¹ * gaussianWeight (4*a)⁻¹ z

lemma heatKernel_nonneg {a : ℝ} (ha : 0 ≤ a) (z : Plane) : 0 ≤ heatKernel a z := by
  unfold heatKernel
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (gaussianWeight_pos _ _).le

lemma integral_gaussianWeight {a : ℝ} (ha : 0 < a) :
    ∫ z : Plane, gaussianWeight a z = Real.pi / a := by
  simpa [gaussianWeight, Plane, finrank_euclideanSpace, Real.rpow_one] using
    (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Plane) ha)

lemma integral_heatKernel {a : ℝ} (ha : 0 < a) : ∫ z : Plane, heatKernel a z = 1 := by
  simp only [heatKernel, integral_const_mul]
  rw [integral_gaussianWeight (inv_pos.mpr (by positivity))]
  field_simp [ha.ne', Real.pi_ne_zero]

lemma integrable_gaussianWeight {a : ℝ} (ha : 0 < a) :
    Integrable (gaussianWeight a) volume := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gaussianWeight ha]
  exact div_ne_zero Real.pi_ne_zero ha.ne'

lemma continuous_heatKernel (a : ℝ) : Continuous (heatKernel a) := by
  unfold heatKernel gaussianWeight
  fun_prop

lemma integrable_heatKernel {a : ℝ} (ha : 0 < a) : Integrable (heatKernel a) volume := by
  apply Integrable.of_integral_ne_zero
  rw [integral_heatKernel ha]
  norm_num

lemma lintegral_heatKernel {a : ℝ} (ha : 0 < a) :
    ∫⁻ z : Plane, ENNReal.ofReal (heatKernel a z) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel ha)
    (Eventually.of_forall (heatKernel_nonneg ha.le)), integral_heatKernel ha]
  simp

lemma lintegral_heatKernel_le_of_ball (μ : Measure Plane) (C : ℝ≥0)
    (hball : ∀ r : ℝ, 0 < r → μ (ball 0 r) ≤ (C : ℝ≥0∞) * volume (ball (0 : Plane) r))
    {a : ℝ} (ha : 0 < a) :
    ∫⁻ z, ENNReal.ofReal (heatKernel a z) ∂μ ≤ C := by
  have hp : 0 ≤ (4 * Real.pi * a)⁻¹ := inv_nonneg.mpr (by positivity)
  have hg (ν : Measure Plane) :
      ∫⁻ z, ENNReal.ofReal (heatKernel a z) ∂ν =
        ENNReal.ofReal ((4 * Real.pi * a)⁻¹) *
          ∫⁻ z, ENNReal.ofReal (gaussianWeight (4*a)⁻¹ z) ∂ν := by
    simp only [heatKernel, ENNReal.ofReal_mul hp]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal ((4 * Real.pi * a)⁻¹) *
        ((C : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (gaussianWeight (4*a)⁻¹ z)) := by
      rw [hg]
      exact mul_le_mul_right (lintegral_gaussianWeight_le_of_ball μ volume C hball
        (inv_pos.mpr (by positivity))) _
    _ = (C : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal (heatKernel a z) := by rw [hg]; ring
    _ = C := by rw [lintegral_heatKernel ha, mul_one]

lemma heat_mul_le_of_ball {h : Plane → ℝ} (hm : AEStronglyMeasurable h volume)
    (hn : ∀ z, 0 ≤ h z) (C : ℝ≥0)
    (hball : ∀ r : ℝ, 0 < r →
      ∫⁻ z in ball (0 : Plane) r, ENNReal.ofReal (h z) ≤
        (C : ℝ≥0∞) * volume (ball (0 : Plane) r))
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun z => heatKernel a z * h z) volume ∧
      ∫ z, heatKernel a z * h z ≤ C := by
  let μ := volume.withDensity (fun z => ENNReal.ofReal (h z))
  have hb : ∀ r : ℝ, 0 < r → μ (ball 0 r) ≤
      (C : ℝ≥0∞) * volume (ball (0 : Plane) r) := by
    intro r hr
    simpa only [μ, withDensity_apply _ measurableSet_ball] using hball r hr
  have hlin : ∫⁻ z, ENNReal.ofReal (heatKernel a z * h z) ≤ C := by
    have hh := lintegral_heatKernel_le_of_ball μ C hb ha
    dsimp only [μ] at hh
    have he := lintegral_withDensity_eq_lintegral_mul₀
      (ENNReal.continuous_ofReal.measurable.comp_aemeasurable hm.aemeasurable)
      (ENNReal.continuous_ofReal.comp (continuous_heatKernel a)).aemeasurable
    simp only [Function.comp_def, Pi.mul_apply] at he
    rw [he] at hh
    have heq (z : Plane) : ENNReal.ofReal (heatKernel a z * h z) =
        ENNReal.ofReal (h z) * ENNReal.ofReal (heatKernel a z) := by
      rw [ENNReal.ofReal_mul (heatKernel_nonneg ha.le z), mul_comm]
    simpa only [heq] using hh
  have hnon : 0 ≤ᵐ[volume] (fun z => heatKernel a z * h z) :=
    Eventually.of_forall fun z => mul_nonneg (heatKernel_nonneg ha.le z) (hn z)
  have hi : Integrable (fun z => heatKernel a z * h z) volume :=
    ⟨(continuous_heatKernel a).aestronglyMeasurable.mul hm,
      (hasFiniteIntegral_iff_ofReal hnon).2 (hlin.trans_lt ENNReal.coe_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnon hi.aestronglyMeasurable]
  exact ENNReal.toReal_mono ENNReal.coe_ne_top hlin

lemma cutoff_ball_mass {h : Plane → ℝ} (hn : ∀ z, 0 ≤ h z)
    (C : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ r : ℝ, 0 < r → r ≤ ρ →
      ∫⁻ z in ball (0 : Plane) r, ENNReal.ofReal (h z) ≤
        (C : ℝ≥0∞) * volume (ball (0 : Plane) r))
    (r : ℝ) (hr : 0 < r) :
    ∫⁻ z in ball (0 : Plane) r,
        ENNReal.ofReal ((ball (0 : Plane) ρ).indicator h z) ≤
      (C : ℝ≥0∞) * volume (ball (0 : Plane) r) := by
  by_cases hrs : r ≤ ρ
  · apply le_trans _ (hball r hr hrs)
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    by_cases hz : z ∈ ball (0 : Plane) ρ <;> simp [hz, hn z]
  · have hle : ρ ≤ r := le_of_not_ge hrs
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal ((ball (0 : Plane) ρ).indicator h z) :=
        setLIntegral_le_lintegral _ _
      _ = ∫⁻ z in ball (0 : Plane) ρ, ENNReal.ofReal (h z) := by
        have he : (fun z => ENNReal.ofReal ((ball (0 : Plane) ρ).indicator h z)) =
            (ball (0 : Plane) ρ).indicator (fun z => ENNReal.ofReal (h z)) := by
          ext z
          by_cases hz : z ∈ ball (0 : Plane) ρ <;> simp [hz]
        rw [he, lintegral_indicator measurableSet_ball]
      _ ≤ (C : ℝ≥0∞) * volume (ball (0 : Plane) ρ) := hball ρ hρ le_rfl
      _ ≤ (C : ℝ≥0∞) * volume (ball (0 : Plane) r) := by
        exact mul_le_mul_right (measure_mono (ball_subset_ball hle)) _

lemma heat_mul_cutoff_le {h : Plane → ℝ} (hm : AEStronglyMeasurable h volume)
    (hn : ∀ z, 0 ≤ h z) (C : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ r : ℝ, 0 < r → r ≤ ρ →
      ∫⁻ z in ball (0 : Plane) r, ENNReal.ofReal (h z) ≤
        (C : ℝ≥0∞) * volume (ball (0 : Plane) r))
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun z => heatKernel a z * (ball (0 : Plane) ρ).indicator h z) volume ∧
      ∫ z, heatKernel a z * (ball (0 : Plane) ρ).indicator h z ≤ C := by
  exact heat_mul_le_of_ball (hm.indicator measurableSet_ball)
    (fun z => indicator_nonneg (fun y _ => hn y) z) C
    (cutoff_ball_mass hn C hρ hball) ha

def heatTailCoefficient (a ρ : ℝ) : ℝ :=
  (4 * Real.pi * a)⁻¹ * Real.exp (-(ρ ^ 2) / (8*a))

lemma heatTailCoefficient_nonneg {a : ℝ} (ha : 0 ≤ a) (ρ : ℝ) :
    0 ≤ heatTailCoefficient a ρ := by
  unfold heatTailCoefficient
  positivity

lemma heatKernel_le_tail {a b ρ : ℝ} (ha : 0 < a) (hρ : 0 ≤ ρ)
    (hab : 8 * a * b ≤ 1) (z : Plane) (hz : ρ ≤ ‖z‖) :
    heatKernel a z ≤ heatTailCoefficient a ρ * gaussianWeight b z := by
  have hc : b ≤ (8*a)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by positivity : 0 < 8*a)]
    nlinarith [hab]
  have hn : ρ^2 ≤ ‖z‖^2 := by nlinarith [norm_nonneg z]
  have hh : -(4*a)⁻¹ * ‖z‖^2 ≤ -(ρ^2) / (8*a) + -b * ‖z‖^2 := by
    have h1 := mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr
      (inv_nonneg.mpr (by positivity : 0 ≤ 8*a)))
    have h2 := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖z‖)
    have he : (4*a)⁻¹ = 2*(8*a)⁻¹ := by field_simp; ring
    rw [he]
    rw [div_eq_mul_inv]
    nlinarith [h1, h2]
  unfold heatKernel heatTailCoefficient gaussianWeight
  rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh) (by positivity)

lemma heatTailCoefficient_tendsto {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun a : ℝ => heatTailCoefficient a ρ) (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun a : ℝ => (ρ^2/8) * a⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by positivity)
  have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu).const_mul
    (2 / (Real.pi * ρ^2))
  simp only [pow_one, mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have han : a ≠ 0 := ne_of_gt ha
  dsimp only [Function.comp_def]
  unfold heatTailCoefficient
  have he : -(ρ^2) / (8*a) = -((ρ^2/8) * a⁻¹) := by field_simp
  rw [he]
  field_simp
  ring

lemma heat_mul_tail_bound {h : Plane → ℝ} (hm : AEStronglyMeasurable h volume)
    (hn : ∀ z, 0 ≤ h z) {b ρ a : ℝ} (hρ : 0 ≤ ρ) (ha : 0 < a)
    (hab : 8 * a * b ≤ 1) (hi : Integrable (fun z => gaussianWeight b z * h z) volume) :
    IntegrableOn (fun z => heatKernel a z * h z) (ball (0 : Plane) ρ)ᶜ volume ∧
      ∫ z in (ball (0 : Plane) ρ)ᶜ, heatKernel a z * h z ≤
        heatTailCoefficient a ρ * ∫ z, gaussianWeight b z * h z := by
  have maj : IntegrableOn (fun z => heatTailCoefficient a ρ * (gaussianWeight b z * h z))
      (ball (0 : Plane) ρ)ᶜ volume :=
    (hi.const_mul (heatTailCoefficient a ρ)).integrableOn
  have hbound : ∀ᵐ z ∂volume.restrict (ball (0 : Plane) ρ)ᶜ,
      ‖heatKernel a z * h z‖ ≤ heatTailCoefficient a ρ * (gaussianWeight b z * h z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with z hz
    have hz' : ρ ≤ ‖z‖ := by simpa [mem_ball, dist_zero_right, not_lt] using hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_nonneg ha.le z) (hn z))]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (heatKernel_le_tail ha hρ hab z hz') (hn z)
  have hInt : IntegrableOn (fun z => heatKernel a z * h z) (ball (0 : Plane) ρ)ᶜ volume :=
    maj.mono' ((continuous_heatKernel a).aestronglyMeasurable.mul hm).restrict hbound
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ z in (ball (0 : Plane) ρ)ᶜ,
        heatTailCoefficient a ρ * (gaussianWeight b z * h z) := by
      apply integral_mono_ae hInt maj
      filter_upwards [hbound] with z hz using (le_abs_self _).trans hz
    _ = heatTailCoefficient a ρ * ∫ z in (ball (0 : Plane) ρ)ᶜ,
        gaussianWeight b z * h z := by rw [integral_const_mul]
    _ ≤ heatTailCoefficient a ρ * ∫ z, gaussianWeight b z * h z := by
      apply mul_le_mul_of_nonneg_left _ (heatTailCoefficient_nonneg ha.le ρ)
      exact setIntegral_le_integral hi (Eventually.of_forall fun z =>
        mul_nonneg (gaussianWeight_pos b z).le (hn z))

lemma tendsto_heat_mul_tail {h : Plane → ℝ} (hm : AEStronglyMeasurable h volume)
    (hn : ∀ z, 0 ≤ h z) {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (hi : Integrable (fun z => gaussianWeight b z * h z) volume) :
    Tendsto (fun a : ℝ => ∫ z in (ball (0 : Plane) ρ)ᶜ, heatKernel a z * h z)
      (𝓝[>] 0) (𝓝 0) := by
  have hc := (heatTailCoefficient_tendsto hρ).mul_const
    (∫ z, gaussianWeight b z * h z)
  rw [zero_mul] at hc
  refine squeeze_zero' ?_ ?_ hc
  · filter_upwards [self_mem_nhdsWithin] with a ha
    exact integral_nonneg fun z => mul_nonneg (heatKernel_nonneg (le_of_lt ha) z) (hn z)
  · have he : ∀ᶠ a : ℝ in 𝓝[>] 0, a < (8*b)⁻¹ :=
      (eventually_lt_nhds (inv_pos.mpr (by positivity : 0 < 8*b))).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, he] with a ha hab
    apply (heat_mul_tail_bound hm hn hρ.le ha _ hi).2
    rw [inv_eq_one_div, lt_div_iff₀ (by positivity : 0 < 8*b)] at hab
    nlinarith

lemma heat_mul_cutoff_eq (h : Plane → ℝ) (a ρ : ℝ) :
    (fun z => heatKernel a z * (ball (0 : Plane) ρ).indicator h z) =
      (ball (0 : Plane) ρ).indicator (fun z => heatKernel a z * h z) := by
  ext z
  by_cases hz : z ∈ ball (0 : Plane) ρ <;> simp [hz]

lemma tendsto_heat_mul_zero_of_small_balls {h : Plane → ℝ}
    (hm : AEStronglyMeasurable h volume) (hn : ∀ z, 0 ≤ h z)
    {b : ℝ} (hb : 0 < b) (hi : Integrable (fun z => gaussianWeight b z * h z) volume)
    (hsmall : ∀ C : ℝ≥0, 0 < C → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r : ℝ, 0 < r → r ≤ ρ →
        ∫⁻ z in ball (0 : Plane) r, ENNReal.ofReal (h z) ≤
          (C : ℝ≥0∞) * volume (ball (0 : Plane) r)) :
    Tendsto (fun a : ℝ => ∫ z, heatKernel a z * h z) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let C : ℝ≥0 := ⟨ε/2, (half_pos hε).le⟩
  obtain ⟨ρ, hρ, hball⟩ := hsmall C (half_pos hε)
  have htail := tendsto_heat_mul_tail hm hn hb hρ hi
  have htail' : ∀ᶠ a : ℝ in 𝓝[>] 0,
      ∫ z in (ball (0 : Plane) ρ)ᶜ, heatKernel a z * h z < ε/2 :=
    htail.eventually (eventually_lt_nhds (half_pos hε))
  have he : ∀ᶠ a : ℝ in 𝓝[>] 0, a < (8*b)⁻¹ :=
    (eventually_lt_nhds (inv_pos.mpr (by positivity : 0 < 8*b))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, he, htail'] with a ha hab htaila
  have hab' : 8*a*b ≤ 1 := by
    rw [inv_eq_one_div, lt_div_iff₀ (by positivity : 0 < 8*b)] at hab
    nlinarith
  obtain ⟨hloc, hlocBound⟩ := heat_mul_cutoff_le hm hn C hρ hball ha
  rw [heat_mul_cutoff_eq h a ρ] at hloc hlocBound
  rw [integral_indicator measurableSet_ball] at hlocBound
  have hloc' := (integrable_indicator_iff measurableSet_ball).mp hloc
  have hfar := (heat_mul_tail_bound hm hn hρ.le ha hab' hi).1
  have hiAll : Integrable (fun z => heatKernel a z * h z) volume := by
    have hh := hloc'.union hfar
    simpa only [union_compl_self, integrableOn_univ] using hh
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg
    (fun z => mul_nonneg (heatKernel_nonneg (le_of_lt ha) z) (hn z))),
    ← integral_add_compl (s := ball (0 : Plane) ρ) measurableSet_ball hiAll]
  change ∫ z in ball (0 : Plane) ρ, heatKernel a z * h z ≤ ε/2 at hlocBound
  linarith

lemma small_ball_mass_of_tendsto_average {h : Plane → ℝ}
    (hloc : LocallyIntegrable h volume) (hn : ∀ z, 0 ≤ h z)
    (hlim : Tendsto (fun r : ℝ => (Real.pi*r^2)⁻¹ * ∫ z in ball (0 : Plane) r, h z)
      (𝓝[>] 0) (𝓝 0)) (C : ℝ≥0) (hC : 0 < C) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r ≤ ρ →
      ∫⁻ z in ball (0 : Plane) r, ENNReal.ofReal (h z) ≤
        (C : ℝ≥0∞) * volume (ball (0 : Plane) r) := by
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (Real.pi*r^2)⁻¹ * (∫ z in ball (0 : Plane) r, h z) < (C : ℝ) :=
    hlim.eventually (eventually_lt_nhds hC)
  obtain ⟨ρ, hρ, hr⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
  refine ⟨ρ, hρ, fun r hr0 hrr => ?_⟩
  have hr' : (Real.pi*r^2)⁻¹ * (∫ z in ball (0 : Plane) r, h z) < (C : ℝ) :=
    hr ⟨hr0, hrr⟩
  have hbound := hr'.le
  have hrpos : 0 < Real.pi * r^2 := by positivity
  have hreal : (∫ z in ball (0 : Plane) r, h z) ≤ (C : ℝ) * (Real.pi*r^2) := by
    exact (inv_mul_le_iff₀' hrpos).mp hbound
  have hi := (hloc.integrableOn_isCompact (isCompact_closedBall (0 : Plane) r)).mono_set
    ball_subset_closedBall
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)]
  have hv : (C : ℝ≥0∞) * volume (ball (0 : Plane) r) =
      ENNReal.ofReal ((C : ℝ) * (Real.pi*r^2)) := by
    rw [EuclideanSpace.volume_ball_fin_two]
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_mul Real.pi_nonneg,
      ENNReal.ofReal_pow hr0.le]
    simp only [ENNReal.ofReal_coe_nnreal]
    ring
  rw [hv]
  exact ENNReal.ofReal_le_ofReal hreal

lemma tendsto_heat_mul_zero_of_lebesgue {h : Plane → ℝ}
    (hm : AEStronglyMeasurable h volume) (hloc : LocallyIntegrable h volume)
    (hn : ∀ z, 0 ≤ h z) {b : ℝ} (hb : 0 < b)
    (hi : Integrable (fun z => gaussianWeight b z * h z) volume)
    (hlim : Tendsto (fun r : ℝ => (Real.pi*r^2)⁻¹ * ∫ z in ball (0 : Plane) r, h z)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun a : ℝ => ∫ z, heatKernel a z * h z) (𝓝[>] 0) (𝓝 0) :=
  tendsto_heat_mul_zero_of_small_balls hm hn hb hi
    (small_ball_mass_of_tendsto_average hloc hn hlim)

lemma gaussianWeight_lower_on_unit_ball {b : ℝ} (hb : 0 ≤ b) (x y : Plane)
    (hx : x ∈ ball y 1) :
    Real.exp (-b) * gaussianWeight b y ≤ gaussianWeight (b/2) x := by
  have hx' : dist x y < 1 := hx
  have hn : ‖x‖ ≤ ‖y‖ + 1 := by
    calc
      ‖x‖ = ‖(x-y)+y‖ := by congr 1; abel
      _ ≤ ‖x-y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ ‖y‖ + 1 := by rw [← dist_eq_norm]; linarith
  have hs : ‖x‖^2 ≤ 2*‖y‖^2 + 2 := by
    have hxy : ‖x‖^2 ≤ (‖y‖+1)^2 := by
      nlinarith [norm_nonneg x, norm_nonneg y]
    nlinarith [sq_nonneg (‖y‖-1)]
  unfold gaussianWeight
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left hs hb]

lemma gaussianWeight_lintegral_unit_ball_lower {b : ℝ} (hb : 0 ≤ b) (y : Plane) :
    ENNReal.ofReal (Real.pi * Real.exp (-b)) * ENNReal.ofReal (gaussianWeight b y) ≤
      ∫⁻ x in ball y 1, ENNReal.ofReal (gaussianWeight (b/2) x) := by
  calc
    _ = ∫⁻ x in ball y 1, ENNReal.ofReal (Real.exp (-b) * gaussianWeight b y) := by
      rw [lintegral_const, Measure.restrict_apply_univ,
        EuclideanSpace.volume_ball_fin_two]
      simp only [ENNReal.ofReal_one, one_pow, one_mul,
        ENNReal.ofReal_mul Real.pi_nonneg, ENNReal.ofReal_mul (Real.exp_pos _).le]
      ring
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact ENNReal.ofReal_le_ofReal (gaussianWeight_lower_on_unit_ball hb x y hx)

lemma lintegral_gaussian_mul_lt_top_of_unit_ball_mass
    {H : Plane → ℝ≥0∞} (hH : AEMeasurable H volume) (A : ℝ≥0)
    (hball : ∀ x : Plane, ∫⁻ y in ball x 1, H y ≤ A) {b : ℝ} (hb : 0 < b) :
    ∫⁻ y, ENNReal.ofReal (gaussianWeight b y) * H y < ⊤ := by
  let G : Plane → ℝ≥0∞ := fun x => ENNReal.ofReal (gaussianWeight (b/2) x)
  have hG : Measurable G := by dsimp [G, gaussianWeight]; fun_prop
  let F : Plane → Plane → ℝ≥0∞ := fun x y => G x * (ball x 1).indicator H y
  have hF : AEMeasurable (Function.uncurry F) (volume.prod volume) := by
    have hs : MeasurableSet {p : Plane × Plane | dist p.2 p.1 < 1} :=
      measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const
    have hh : AEMeasurable (fun p : Plane × Plane => G p.1 *
        {p : Plane × Plane | dist p.2 p.1 < 1}.indicator (fun p => H p.2) p)
        (volume.prod volume) :=
      (hG.comp measurable_fst).aemeasurable.mul (hH.comp_snd.indicator hs)
    convert hh using 1
    ext p
    by_cases hp : dist p.2 p.1 < 1 <;> simp [F, Function.uncurry_def, mem_ball, hp]
  have hleft (x : Plane) : ∫⁻ y, F x y = G x * ∫⁻ y in ball x 1, H y := by
    dsimp only [F]
    rw [lintegral_const_mul' _ _ (by exact ENNReal.ofReal_ne_top),
      lintegral_indicator measurableSet_ball]
  have hright (y : Plane) : ∫⁻ x, F x y = (∫⁻ x in ball y 1, G x) * H y := by
    have he : (fun x => F x y) = (ball y 1).indicator (fun x => G x * H y) := by
      ext x
      by_cases hx : dist x y < 1 <;> simp [F, mem_ball, dist_comm y x, hx]
    rw [he, lintegral_indicator measurableSet_ball, lintegral_mul_const _ hG]
  have hswap := lintegral_lintegral_swap hF
  simp only [hleft, hright] at hswap
  have hupper : ∫⁻ y, (∫⁻ x in ball y 1, G x) * H y ≤
      (∫⁻ x, G x) * (A : ℝ≥0∞) := by
    rw [← hswap, ← lintegral_mul_const' _ _ ENNReal.coe_ne_top]
    exact lintegral_mono fun x => mul_le_mul_right (hball x) _
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.pi * Real.exp (-b))
  have hC : C ≠ 0 := by dsimp [C]; positivity
  have hClt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hlower : C * ∫⁻ y, ENNReal.ofReal (gaussianWeight b y) * H y ≤
      ∫⁻ y, (∫⁻ x in ball y 1, G x) * H y := by
    rw [← lintegral_const_mul' _ _ hClt]
    apply lintegral_mono
    intro y
    dsimp only
    rw [← mul_assoc]
    exact mul_le_mul_left (gaussianWeight_lintegral_unit_ball_lower hb.le y) _
  have hgfin : ∫⁻ x, G x < ⊤ := by
    dsimp only [G]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianWeight (half_pos hb))
      (Eventually.of_forall fun x => (gaussianWeight_pos _ x).le)]
    exact ENNReal.ofReal_lt_top
  have hfin := hlower.trans_lt (hupper.trans_lt (ENNReal.mul_lt_top hgfin ENNReal.coe_lt_top))
  exact ENNReal.lt_top_of_mul_ne_top_right hfin.ne hC

lemma integrable_gaussian_mul_of_unit_ball_mass {h : Plane → ℝ}
    (hloc : LocallyIntegrable h volume) (hn : ∀ z, 0 ≤ h z) (A : ℝ≥0)
    (hball : ∀ x : Plane, ∫ y in ball x 1, h y ≤ A) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z => gaussianWeight b z * h z) volume := by
  have hm := hloc.aestronglyMeasurable
  have hb' (x : Plane) : ∫⁻ y in ball x 1, ENNReal.ofReal (h y) ≤ A := by
    have hi := (hloc.integrableOn_isCompact (isCompact_closedBall x 1)).mono_set ball_subset_closedBall
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)]
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hball x)
  have hh := lintegral_gaussian_mul_lt_top_of_unit_ball_mass
    (ENNReal.continuous_ofReal.measurable.comp_aemeasurable hm.aemeasurable) A hb' hb
  refine ⟨(by unfold gaussianWeight; fun_prop : Continuous (gaussianWeight b)).aestronglyMeasurable.mul hm, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
    mul_nonneg (gaussianWeight_pos b z).le (hn z))]
  simpa only [Function.comp_def, ENNReal.ofReal_mul (gaussianWeight_pos b _).le] using hh

lemma reflect_preimage_ball (x y : Plane) (r : ℝ) :
    (fun z : Plane => x-z) ⁻¹' ball y r = ball (x-y) r := by
  ext z
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  have he : x-z-y = -(z-(x-y)) := by abel
  rw [he, norm_neg]

lemma locallyIntegrable_reflect {h : Plane → ℝ}
    (hloc : LocallyIntegrable h volume) (x : Plane) :
    LocallyIntegrable (fun z => h (x-z)) volume := by
  intro y
  refine ⟨ball y 1, ball_mem_nhds y zero_lt_one, ?_⟩
  have hi := (hloc.integrableOn_isCompact (isCompact_closedBall (x-y) 1)).mono_set
    ball_subset_closedBall
  have hm := (volume.measurePreserving_sub_left x).restrict_preimage
    (measurableSet_ball (x := x-y) (ε := (1 : ℝ)))
  have hh := (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  simpa only [IntegrableOn, Function.comp_def, reflect_preimage_ball, sub_sub_cancel] using hh

lemma integral_reflect_ball (h : Plane → ℝ) (x y : Plane) (r : ℝ) :
    ∫ z in ball y r, h (x-z) = ∫ z in ball (x-y) r, h z := by
  have hm := (volume.measurePreserving_sub_left x).restrict_preimage
    (measurableSet_ball (x := x-y) (ε := r))
  have hh := hm.integral_comp (MeasurableEquiv.subLeft x).measurableEmbedding h
  simpa only [reflect_preimage_ball, sub_sub_cancel] using hh

lemma integrable_heat_mul_of_unit_ball_mass {h : Plane → ℝ}
    (hloc : LocallyIntegrable h volume) (hn : ∀ z, 0 ≤ h z) (A : ℝ≥0)
    (hball : ∀ x : Plane, ∫ y in ball x 1, h y ≤ A) {a : ℝ} (ha : 0 < a) :
    Integrable (fun z => heatKernel a z * h z) volume := by
  have hh := integrable_gaussian_mul_of_unit_ball_mass hloc hn A hball
    (show 0 < (4*a)⁻¹ by positivity)
  simpa only [heatKernel, mul_assoc] using hh.const_mul (4*Real.pi*a)⁻¹

lemma heat_envelope {h : Plane → ℝ}
    (hloc : LocallyIntegrable h volume) (hn : ∀ z, 0 ≤ h z) (A : ℝ≥0)
    (hball : ∀ x : Plane, ∫ y in ball x 1, h y ≤ A) (x : Plane) :
    (∀ a : ℝ, 0 < a → Integrable (fun z => heatKernel a z * h (x-z)) volume) ∧
    (Tendsto (fun r : ℝ => (Real.pi*r^2)⁻¹ *
      ∫ y in ball x r, |h y-h x|) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun a : ℝ => ∫ z, heatKernel a z * h (x-z)) (𝓝[>] 0) (𝓝 (h x))) := by
  have hloc' := locallyIntegrable_reflect hloc x
  have hn' : ∀ z, 0 ≤ h (x-z) := fun z => hn _
  have hball' (y : Plane) : ∫ z in ball y 1, h (x-z) ≤ A := by
    rw [integral_reflect_ball]
    exact hball _
  have hfinite : ∀ a : ℝ, 0 < a →
      Integrable (fun z => heatKernel a z * h (x-z)) volume :=
    fun a ha => integrable_heat_mul_of_unit_ball_mass hloc' hn' A hball' ha
  refine ⟨hfinite, ?_⟩
  intro hlim
  let e : Plane → ℝ := fun z => |h (x-z)-h x|
  have eloc : LocallyIntegrable e volume := by
    rw [← locallyIntegrableOn_univ]
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      ((hloc'.sub (locallyIntegrable_const (h x))).locallyIntegrableOn univ).norm
  have en : ∀ z, 0 ≤ e z := fun z => abs_nonneg _
  have emean : Tendsto (fun r : ℝ => (Real.pi*r^2)⁻¹ * ∫ z in ball (0 : Plane) r, e z)
      (𝓝[>] 0) (𝓝 0) := by
    have heq (r : ℝ) : (∫ z in ball (0 : Plane) r, e z) =
        ∫ y in ball x r, |h y-h x| := by
      simpa only [e, sub_zero] using integral_reflect_ball (fun y => |h y-h x|) x 0 r
    simpa only [heq] using hlim
  have eg : Integrable (fun z => gaussianWeight 1 z * e z) volume := by
    have hgi := integrable_gaussian_mul_of_unit_ball_mass hloc' hn' A hball' zero_lt_one
    have hconst := (integrable_gaussianWeight zero_lt_one).mul_const |h x|
    refine (hgi.add hconst).mono' ((by unfold gaussianWeight; fun_prop :
      Continuous (gaussianWeight 1)).aestronglyMeasurable.mul eloc.aestronglyMeasurable) ?_
    filter_upwards [] with z
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianWeight_pos _ _).le (en z)),
      ← mul_add]
    apply mul_le_mul_of_nonneg_left _ (gaussianWeight_pos _ _).le
    dsimp only [e]
    have hh := abs_sub_le (h (x-z)) 0 (h x)
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (hn (x-z))] using hh
  have he := tendsto_heat_mul_zero_of_lebesgue eloc.aestronglyMeasurable eloc en
    zero_lt_one eg emean
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hε' := he.eventually (eventually_lt_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hε'] with a ha hae
  have hc := (integrable_heatKernel ha).mul_const (h x)
  have hi := (hfinite a ha).sub hc
  have heq : (∫ z, heatKernel a z * h (x-z)) - h x =
      ∫ z, heatKernel a z * (h (x-z)-h x) := by
    simp_rw [mul_sub]
    rw [integral_sub (hfinite a ha) hc, integral_mul_const, integral_heatKernel ha, one_mul]
  rw [Real.dist_eq, heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ z, ‖heatKernel a z * (h (x-z)-h x)‖ := norm_integral_le_integral_norm _
    _ = ∫ z, heatKernel a z * e z := by
      congr 1
      ext z
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ha.le z)]
      rfl
    _ < ε := hae

end PlanarEndpoint
end

end OAI
