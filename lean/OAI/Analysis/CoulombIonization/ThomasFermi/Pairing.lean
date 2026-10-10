import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.Tensor

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
section Pairing
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def tfPairing (w : α → ℝ) (hw : MemLp w (5 / 2) μ) : TFLp μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ (5 / 2) (5 / 3) (hw.toLp w)

lemma tfPairing_apply (w : α → ℝ) (hw : MemLp w (5 / 2) μ) (f : TFLp μ) :
    tfPairing w hw f = ∫ x, w x * f x ∂μ := by
  rw [tfPairing, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hw.coeFn_toLp] with x hx
  exact congrArg (fun c => c * f x) hx

lemma tfPairing_integrable (w : α → ℝ) (hw : MemLp w (5 / 2) μ) (f : TFLp μ) :
    Integrable (fun x => w x * f x) μ := by
  exact hw.integrable_mul (Lp.memLp f)

end Pairing

def tfCoulombL (R : ℝ) : TFLp (ballMeasure R) →L[ℝ] TFLp (ballMeasure R) →L[ℝ] ℝ :=
  ((tfPairing (fun p : TFSpace × TFSpace => ‖p.1 - p.2‖⁻¹) (coulomb_memLp R)).postcomp
    (TFLp (ballMeasure R))).comp tfTensorL

lemma tfCoulombL_apply (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R f g = ∫ p : TFSpace × TFSpace, f p.1 * g p.2 / ‖p.1 - p.2‖
      ∂((ballMeasure R).prod (ballMeasure R)) := by
  change tfPairing _ _ (tfTensor f g) = _
  rw [tfPairing_apply]
  apply integral_congr_ae
  filter_upwards [tfTensor_coe f g] with p hp
  rw [hp, div_eq_mul_inv (f p.1 * g p.2) ‖p.1 - p.2‖, mul_comm]

lemma tfCoulomb_integrable (R : ℝ) (f g : TFLp (ballMeasure R)) :
    Integrable (fun p : TFSpace × TFSpace => f p.1 * g p.2 / ‖p.1 - p.2‖)
      ((ballMeasure R).prod (ballMeasure R)) := by
  have hi := tfPairing_integrable _ (coulomb_memLp R) (tfTensor f g)
  apply hi.congr
  filter_upwards [tfTensor_coe f g] with p hp
  rw [hp, div_eq_mul_inv (f p.1 * g p.2) ‖p.1 - p.2‖, mul_comm]


open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E]

def gaussian (b : ℝ) (x : E) : ℝ := Real.exp (-b * ‖x‖ ^ 2)

lemma gaussian_pos (b : ℝ) (x : E) : 0 < gaussian b x := Real.exp_pos _

lemma gaussian_bound {b : ℝ} (hb : 0 ≤ b) (x : E) : gaussian b x ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _))

lemma gaussian_continuous (b : ℝ) : Continuous (gaussian b : E → ℝ) := by
  unfold gaussian
  fun_prop

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma gaussian_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : E, gaussian b x) = (Real.pi / b) ^ ((Module.finrank ℝ E : ℝ) / 2) :=
  GaussianFourier.integral_rexp_neg_mul_sq_norm hb

lemma gaussian_integrable {b : ℝ} (hb : 0 < b) : Integrable (gaussian b : E → ℝ) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussian_integral hb]
  exact ne_of_gt (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussian_overlap (b : ℝ) (x y z : E) :
    gaussian (2 * b) (z - x) * gaussian (2 * b) (z - y) =
      gaussian b (x - y) * gaussian (4 * b) (z - (1 / 2 : ℝ) • (x + y)) := by
  simp only [gaussian, ← Real.exp_add]
  congr 1
  simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_right,
    real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma gaussian_overlap_integral {b : ℝ} (hb : 0 < b) (x y : E) :
    (∫ z : E, gaussian (2 * b) (z - x) * gaussian (2 * b) (z - y)) =
      gaussian b (x - y) * (Real.pi / (4 * b)) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  simp_rw [gaussian_overlap]
  rw [integral_const_mul, integral_sub_right_eq_self, gaussian_integral (by positivity)]

lemma gaussian_overlap_integrable {b : ℝ} (hb : 0 < b) (x y : E) :
    Integrable (fun z : E => gaussian (2 * b) (z - x) * gaussian (2 * b) (z - y)) := by
  simp_rw [gaussian_overlap]
  exact ((gaussian_integrable (E := E) (show 0 < 4 * b by positivity)).comp_sub_right
    ((1 / 2 : ℝ) • (x + y))).const_mul _

lemma integrable_gaussian_quadratic {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun p : E × E => f p.1 * f p.2 * gaussian b (p.1 - p.2)) := by
  apply (hf.mul_prod hf).mul_bdd (c := 1) ((gaussian_continuous b).comp
    (continuous_fst.sub continuous_snd)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖gaussian b (p.1 - p.2)‖ ≤ 1
    rw [Real.norm_of_nonneg (gaussian_pos b _).le]
    exact gaussian_bound hb _

lemma integrable_gaussian_triple {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : (E × E) × E => (f p.1.1 * f p.1.2) *
      (gaussian (2 * b) (p.2 - p.1.1) * gaussian (2 * b) (p.2 - p.1.2))) := by
  have hm : AEStronglyMeasurable (fun p : (E × E) × E => (f p.1.1 * f p.1.2) *
      (gaussian (2 * b) (p.2 - p.1.1) * gaussian (2 * b) (p.2 - p.1.2))) := by
    exact ((hf.mul_prod hf).aestronglyMeasurable.comp_fst).mul
      (show Continuous (fun p : (E × E) × E =>
        gaussian (2 * b) (p.2 - p.1.1) * gaussian (2 * b) (p.2 - p.1.2)) from by
          unfold gaussian
          fun_prop).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Eventually.of_forall fun p => (gaussian_overlap_integrable hb p.1 p.2).const_mul (f p.1 * f p.2)
  · have he (p : E × E) : (∫ z : E, ‖(f p.1 * f p.2) *
        (gaussian (2 * b) (z - p.1) * gaussian (2 * b) (z - p.2))‖) =
        (‖f p.1‖ * ‖f p.2‖ * gaussian b (p.1 - p.2)) *
          (Real.pi / (4 * b)) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
      simp only [norm_mul, Real.norm_of_nonneg (gaussian_pos _ _).le]
      rw [integral_const_mul, gaussian_overlap_integral hb]
      ring
    simp_rw [he]
    exact (integrable_gaussian_quadratic hf.norm hb.le).mul_const _

theorem gaussian_quadratic_nonneg {f : E → ℝ} (hf : Integrable f) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ ∫ p : E × E, f p.1 * f p.2 * gaussian b (p.1 - p.2) := by
  rcases hb.eq_or_lt with rfl | hb
  · simp only [gaussian, neg_zero, zero_mul, Real.exp_zero, mul_one]
    have h := integral_prod_mul (μ := (volume : Measure E)) (ν := volume) f f
    change 0 ≤ ∫ p : E × E, f p.1 * f p.2 ∂(volume.prod volume)
    rw [h]
    exact mul_self_nonneg (∫ x : E, f x)
  let c : ℝ := (Real.pi / (4 * b)) ^ ((Module.finrank ℝ E : ℝ) / 2)
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have he : (∫ p : E × E, f p.1 * f p.2 * gaussian b (p.1 - p.2)) * c =
      ∫ z : E, (∫ x : E, f x * gaussian (2 * b) (z - x)) ^ 2 := by
    calc
      _ = ∫ p : E × E, ∫ z : E, (f p.1 * f p.2) *
          (gaussian (2 * b) (z - p.1) * gaussian (2 * b) (z - p.2)) := by
        simp_rw [integral_const_mul, gaussian_overlap_integral hb, ← mul_assoc]
        exact (integral_mul_const _ _).symm
      _ = ∫ z : E, ∫ p : E × E, (f p.1 * f p.2) *
          (gaussian (2 * b) (z - p.1) * gaussian (2 * b) (z - p.2)) :=
        integral_integral_swap (integrable_gaussian_triple hf hb)
      _ = _ := by
        apply integral_congr_ae (Eventually.of_forall fun z => ?_)
        have hp : (fun p : E × E => (f p.1 * f p.2) *
            (gaussian (2 * b) (z - p.1) * gaussian (2 * b) (z - p.2))) =
            (fun p : E × E => (f p.1 * gaussian (2 * b) (z - p.1)) *
              (f p.2 * gaussian (2 * b) (z - p.2))) := by
          funext p; ring
        rw [hp, pow_two]
        exact integral_prod_mul (μ := (volume : Measure E)) (ν := volume)
          (fun x => f x * gaussian (2 * b) (z - x))
          (fun x => f x * gaussian (2 * b) (z - x))
  have hh : (0 : ℝ) ≤ ∫ z : E, (∫ x : E, f x * gaussian (2 * b) (z - x)) ^ 2 :=
    integral_nonneg (fun z : E => sq_nonneg (∫ x : E, f x * gaussian (2 * b) (z - x)))
  rw [← he] at hh
  exact nonneg_of_mul_nonneg_left hh hc

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in

lemma coulomb_gaussian_integral (x : E) :
    (∫ t : ℝ, gaussian (t ^ 2) x) = Real.sqrt Real.pi / ‖x‖ := by
  have h (t : ℝ) : gaussian (t ^ 2) x = Real.exp (-(‖x‖ ^ 2) * t ^ 2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [h]
  rw [integral_gaussian, Real.sqrt_div (le_of_lt Real.pi_pos), Real.sqrt_sq (norm_nonneg x)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma coulomb_gaussian_integrable {x : E} (hx : x ≠ 0) :
    Integrable (fun t : ℝ => gaussian (t ^ 2) x) := by
  have h (t : ℝ) : gaussian (t ^ 2) x = Real.exp (-(‖x‖ ^ 2) * t ^ 2) := by
    unfold gaussian
    congr 1
    ring
  simp_rw [h]
  exact integrable_exp_neg_mul_sq (sq_pos_of_pos (norm_pos_iff.mpr hx))

variable [Nontrivial E]

lemma ae_off_diagonal : ∀ᵐ p : E × E, p.1 ≠ p.2 := by
  change ∀ᵐ p ∂(volume : Measure E).prod volume, p.1 ≠ p.2
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
  exact Eventually.of_forall fun x => by
    apply ae_iff.mpr
    have hs : {y : E | ¬ x ≠ y} = {x} := by
      ext y
      simp [eq_comm]
    change volume {a : E | ¬ x ≠ a} = 0
    rw [hs]
    exact measure_singleton x

theorem coulomb_quadratic_nonneg {f : E → ℝ} (hf : Integrable f)
    (hD : Integrable (fun p : E × E => f p.1 * f p.2 / ‖p.1 - p.2‖)) :
    0 ≤ ∫ p : E × E, f p.1 * f p.2 / ‖p.1 - p.2‖ := by
  let F : (E × E) × ℝ → ℝ := fun p => f p.1.1 * f p.1.2 * gaussian (p.2 ^ 2) (p.1.1 - p.1.2)
  have hm : AEStronglyMeasurable F := by
    apply ((hf.mul_prod hf).aestronglyMeasurable.comp_fst).mul
    have hcont : Continuous (fun p : (E × E) × ℝ => gaussian (p.2 ^ 2) (p.1.1 - p.1.2)) := by
      unfold gaussian
      fun_prop
    exact hcont.aestronglyMeasurable
  have hint (p : E × E) : (∫ t : ℝ, ‖F (p, t)‖) =
      ‖f p.1 * f p.2 / ‖p.1 - p.2‖‖ * Real.sqrt Real.pi := by
    simp only [F, norm_mul, Real.norm_of_nonneg (gaussian_pos _ _).le]
    rw [integral_const_mul, coulomb_gaussian_integral]
    simp only [norm_div, norm_mul, norm_norm]
    ring
  have hF : Integrable F := by
    apply (integrable_prod_iff hm).mpr
    constructor
    · filter_upwards [ae_off_diagonal (E := E)] with p hp
      exact (coulomb_gaussian_integrable (sub_ne_zero.mpr hp)).const_mul (f p.1 * f p.2)
    · simp_rw [hint]
      exact hD.norm.mul_const _
  have he : (∫ p : E × E, f p.1 * f p.2 / ‖p.1 - p.2‖) * Real.sqrt Real.pi =
      ∫ t : ℝ, ∫ p : E × E, f p.1 * f p.2 * gaussian (t ^ 2) (p.1 - p.2) := by
    calc
      _ = ∫ p : E × E, ∫ t : ℝ, F (p, t) := by
        simp_rw [F, integral_const_mul, coulomb_gaussian_integral]
        rw [← integral_mul_const]
        apply integral_congr_ae (Eventually.of_forall fun p => ?_)
        ring
      _ = _ := integral_integral_swap hF
  have hn : (0 : ℝ) ≤ ∫ t : ℝ, ∫ p : E × E, f p.1 * f p.2 * gaussian (t ^ 2) (p.1 - p.2) :=
    integral_nonneg fun t => gaussian_quadratic_nonneg hf (sq_nonneg t)
  rw [← he] at hn
  exact nonneg_of_mul_nonneg_left hn (Real.sqrt_pos.mpr Real.pi_pos)

end

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

def tfExtension (R : ℝ) (f : TFLp (ballMeasure R)) : TFSpace → ℝ :=
  (ball 0 R).indicator f

lemma tfExtension_integrable (R : ℝ) (f : TFLp (ballMeasure R)) : Integrable (tfExtension R f) :=
  IntegrableOn.integrable_indicator ((Lp.memLp f).integrable (Fact.out : (1 : ENNReal) ≤ 5 / 3))
    measurableSet_ball

lemma tfExtension_direct (R : ℝ) (f g : TFLp (ballMeasure R)) (p : TFSpace × TFSpace) :
    tfExtension R f p.1 * tfExtension R g p.2 / ‖p.1 - p.2‖ =
      ((ball (0 : TFSpace) R) ×ˢ ball 0 R).indicator
        (fun p : TFSpace × TFSpace => f p.1 * g p.2 / ‖p.1 - p.2‖) p := by
  classical
  by_cases h1 : p.1 ∈ ball (0 : TFSpace) R <;>
    by_cases h2 : p.2 ∈ ball (0 : TFSpace) R <;> simp [tfExtension, h1, h2]

lemma tfExtension_coulomb_integrable (R : ℝ) (f g : TFLp (ballMeasure R)) :
    Integrable (fun p : TFSpace × TFSpace => tfExtension R f p.1 * tfExtension R g p.2 / ‖p.1 - p.2‖) := by
  simp_rw [tfExtension_direct]
  apply IntegrableOn.integrable_indicator _ (measurableSet_ball.prod measurableSet_ball)
  have hi := tfCoulomb_integrable R f g
  simp only [ballMeasure, Measure.prod_restrict] at hi
  exact hi

lemma tfCoulombL_extension (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R f g = ∫ p : TFSpace × TFSpace,
      tfExtension R f p.1 * tfExtension R g p.2 / ‖p.1 - p.2‖ := by
  simp_rw [tfExtension_direct]
  rw [integral_indicator (measurableSet_ball.prod measurableSet_ball), tfCoulombL_apply]
  simp only [ballMeasure, Measure.prod_restrict]
  rfl

lemma tfCoulombL_nonneg (R : ℝ) (f : TFLp (ballMeasure R)) : 0 ≤ tfCoulombL R f f := by
  rw [tfCoulombL_extension]
  exact coulomb_quadratic_nonneg (tfExtension_integrable R f) (tfExtension_coulomb_integrable R f f)

lemma tfCoulombL_symmetric (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfCoulombL R f g = tfCoulombL R g f := by
  rw [tfCoulombL_apply, tfCoulombL_apply]
  rw [← MeasureTheory.integral_prod_swap (f := fun p : TFSpace × TFSpace =>
    g p.1 * f p.2 / ‖p.1 - p.2‖)]
  apply integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp
  rw [norm_sub_rev, mul_comm]

lemma tfCoulombL_midpoint_gap (R : ℝ) (f g : TFLp (ballMeasure R)) :
    0 ≤ (tfCoulombL R f f + tfCoulombL R g g) / 2 -
      tfCoulombL R ((1 / 2 : ℝ) • (f + g)) ((1 / 2 : ℝ) • (f + g)) := by
  have hp := tfCoulombL_nonneg R (f - g)
  simp only [map_sub, sub_apply] at hp
  simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul]
  rw [tfCoulombL_symmetric R g f] at hp ⊢
  linarith

def tfBallLinear (R Z η : ℝ) : TFLp (ballMeasure R) →L[ℝ] ℝ :=
  η • tfPairing (fun _ => (1 : ℝ)) (memLp_const 1) -
    Z • tfPairing (fun x : TFSpace => ‖x‖⁻¹) (nuclear_memLp R)

def tfBallFunctional (R T Z η : ℝ) (f : TFLp (ballMeasure R)) : ℝ :=
  T * ‖f‖ ^ (5 / 3 : ℝ) + tfBallLinear R Z η f + (1 / 2 : ℝ) * tfCoulombL R f f

lemma tfBallFunctional_continuous (R T Z η : ℝ) : Continuous (tfBallFunctional R T Z η) := by
  apply Continuous.add
  · exact ((continuous_norm.rpow_const (fun _ => Or.inr (by norm_num))).const_mul T).add
      (tfBallLinear R Z η).continuous
  · exact ((tfCoulombL R).continuous₂.comp (continuous_id.prodMk continuous_id)).const_mul _

lemma tf_power_dominates_linear {T : ℝ} (hT : 0 < T) (L : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, B ≤ r → r ≤ T * r ^ (5 / 3 : ℝ) - L * r := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).eventually (eventually_ge_atTop ((L + 1) / T)))
  refine ⟨max B 0, le_max_right _ _, fun r hr => ?_⟩
  have hr0 : 0 ≤ r := (le_max_right _ _).trans hr
  have hp := hB r ((le_max_left _ _).trans hr)
  have he : r ^ (5 / 3 : ℝ) = r * r ^ (2 / 3 : ℝ) := by
    rw [show (5 / 3 : ℝ) = 1 + 2 / 3 by norm_num,
      Real.rpow_add_of_nonneg hr0 (by norm_num) (by norm_num), Real.rpow_one]
  rw [div_le_iff₀ hT] at hp
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hp hr0]

lemma tfBallFunctional_lower (R T Z η : ℝ) (f : TFLp (ballMeasure R)) :
    T * ‖f‖ ^ (5 / 3 : ℝ) - ‖tfBallLinear R Z η‖ * ‖f‖ ≤ tfBallFunctional R T Z η f := by
  have hL := (tfBallLinear R Z η).le_opNorm f
  have hn := neg_abs_le (tfBallLinear R Z η f)
  have hD := tfCoulombL_nonneg R f
  change |tfBallLinear R Z η f| ≤ _ at hL
  unfold tfBallFunctional
  linarith

lemma tfBallFunctional_bddBelow (R Z η : ℝ) {T : ℝ} (hT : 0 < T) :
    BddBelow (Set.range (tfBallFunctional R T Z η)) := by
  obtain ⟨B, hB0, hB⟩ := tf_power_dominates_linear hT ‖tfBallLinear R Z η‖
  refine ⟨-‖tfBallLinear R Z η‖ * B, ?_⟩
  rintro _ ⟨f, rfl⟩
  apply le_trans _ (tfBallFunctional_lower R T Z η f)
  by_cases hb : B ≤ ‖f‖
  · exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg _)) hB0).trans
      ((norm_nonneg _).trans (hB _ hb))
  · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hb) (norm_nonneg (tfBallLinear R Z η))
    have hp := mul_nonneg hT.le (Real.rpow_nonneg (norm_nonneg f) (5 / 3 : ℝ))
    linarith

lemma tfBallFunctional_coercive (R Z η a : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ B : ℝ, ∀ f : TFLp (ballMeasure R), tfBallFunctional R T Z η f ≤ a → ‖f‖ ≤ B := by
  obtain ⟨B, _, hB⟩ := tf_power_dominates_linear hT ‖tfBallLinear R Z η‖
  refine ⟨max B a, fun f hf => ?_⟩
  by_cases hb : B ≤ ‖f‖
  · exact ((hB _ hb).trans ((tfBallFunctional_lower R T Z η f).trans hf)).trans (le_max_right _ _)
  · exact (le_of_not_ge hb).trans (le_max_left _ _)

lemma nonnegDensity_smul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : TFLp μ} (hf : NonnegDensity f) {c : ℝ} (hc : 0 ≤ c) : NonnegDensity (c • f) := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx he
  rw [he]
  exact mul_nonneg hc hx

lemma tfLp_midpoint_gap {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : TFLp μ} (hf : NonnegDensity f) (hg : NonnegDensity g) :
    (5 / 36 : ℝ) * densityWeight f g ≤
      (‖f‖ ^ (5 / 3 : ℝ) + ‖g‖ ^ (5 / 3 : ℝ)) / 2 - ‖(1 / 2 : ℝ) • (f + g)‖ ^ (5 / 3 : ℝ) := by
  have hh := tfWeight_integral_gap (Lp.memLp f) (Lp.memLp g) hf hg
  rw [tfLp_norm_rpow_nonneg hf, tfLp_norm_rpow_nonneg hg,
    tfLp_norm_rpow_nonneg (nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num))]
  convert hh using 1
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (f + g), Lp.coeFn_add f g] with x hs ha
  rw [hs, Pi.smul_apply, smul_eq_mul, ha, Pi.add_apply]
  congr 1
  ring

lemma tfBallFunctional_gap (R T Z η : ℝ) (hT : 0 ≤ T) {f g : TFLp (ballMeasure R)}
    (hf : NonnegDensity f) (hg : NonnegDensity g) :
    (T * (5 / 36 : ℝ)) * densityWeight f g ≤
      (tfBallFunctional R T Z η f + tfBallFunctional R T Z η g) / 2 -
        tfBallFunctional R T Z η ((1 / 2 : ℝ) • (f + g)) := by
  have hk := mul_le_mul_of_nonneg_left (tfLp_midpoint_gap hf hg) hT
  have hD := tfCoulombL_midpoint_gap R f g
  unfold tfBallFunctional
  simp only [map_smul, map_add, smul_apply, add_apply, smul_eq_mul] at hD ⊢
  nlinarith

theorem tfBallFunctional_exists_minimizer (R Z η : ℝ) {T : ℝ} (hT : 0 < T) :
    ∃ f : TFLp (ballMeasure R), NonnegDensity f ∧
      ∀ g : TFLp (ballMeasure R), NonnegDensity g →
        tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η g := by
  apply exists_minimizer_of_tf_gap (C := {f | NonnegDensity f}) isClosed_nonnegDensity
  · refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ (5 / 3) (ballMeasure R)] with x hx
    rw [hx]
    exact le_rfl
  · exact fun _ hf => hf
  · exact fun _ hf _ hg => nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num)
  · exact (tfBallFunctional_continuous R T Z η).continuousOn
  · exact (tfBallFunctional_bddBelow R Z η hT).mono (Set.image_subset_range _ _)
  · intro a
    obtain ⟨B, hB⟩ := tfBallFunctional_coercive R Z η a hT
    exact ⟨B, fun f _ hf => hB f hf⟩
  · exact mul_pos hT (by norm_num : (0 : ℝ) < 5 / 36)
  · exact fun _ hf _ hg => tfBallFunctional_gap R T Z η hT.le hf hg

lemma tfBallFunctional_min_unique (R Z η : ℝ) {T : ℝ} (hT : 0 < T)
    {f g : TFLp (ballMeasure R)} (hf : NonnegDensity f) (hg : NonnegDensity g)
    (hminf : ∀ u, NonnegDensity u → tfBallFunctional R T Z η f ≤ tfBallFunctional R T Z η u)
    (hming : ∀ u, NonnegDensity u → tfBallFunctional R T Z η g ≤ tfBallFunctional R T Z η u) : f = g := by
  have hh := nonnegDensity_smul (nonnegDensity_add hf hg) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h1 := hminf _ hh
  have h2 := hming _ hh
  have hgap := tfBallFunctional_gap R T Z η hT.le hf hg
  have hw : densityWeight f g = 0 := by
    apply le_antisymm _ (densityWeight_nonneg hf hg)
    have hp : 0 < T * (5 / 36 : ℝ) := mul_pos hT (by norm_num)
    nlinarith
  have hi := tfLp_interpolation hf hg
  rw [hw, Real.zero_rpow (by norm_num : (5 / 6 : ℝ) ≠ 0), zero_mul] at hi
  have he := le_antisymm hi (Real.rpow_nonneg (norm_nonneg (f - g)) (5 / 3 : ℝ))
  have hz : ‖f - g‖ = 0 := (Real.rpow_eq_zero (norm_nonneg _) (by norm_num)).mp he
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

def tfPowerDerivative (u : ℝ) : ℝ := (5 / 3 : ℝ) * |u| ^ (-1 / 3 : ℝ) * u

lemma tfPowerDerivative_abs (u : ℝ) : |tfPowerDerivative u| = (5 / 3 : ℝ) * |u| ^ (2 / 3 : ℝ) := by
  by_cases hu : u = 0
  · simp [tfPowerDerivative, hu]
  · have ha : 0 < |u| := abs_pos.mpr hu
    rw [tfPowerDerivative, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 3),
      abs_of_nonneg (Real.rpow_nonneg ha.le _)]
    have he := Real.rpow_add ha (-1 / 3) 1
    norm_num at he
    rw [mul_assoc, neg_div, ← he]

lemma tfPowerDerivative_nonneg {u : ℝ} (hu : 0 ≤ u) :
    tfPowerDerivative u = (5 / 3 : ℝ) * u ^ (2 / 3 : ℝ) := by
  rw [← abs_of_nonneg (show 0 ≤ tfPowerDerivative u from by unfold tfPowerDerivative; positivity),
    tfPowerDerivative_abs, abs_of_nonneg hu]

lemma hasDerivAt_tfPower (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => |a + s * b| ^ (5 / 3 : ℝ))
      (tfPowerDerivative (a + t * b) * b) t := by
  have hh : HasDerivAt (fun s : ℝ => a + s * b) b t := by
    simpa using (((hasDerivAt_id t).mul_const b).const_add a)
  have hd := (hasDerivAt_abs_rpow (a + t * b) (by norm_num : (1 : ℝ) < 5 / 3)).comp t hh
  simpa only [Function.comp_def, tfPowerDerivative,
    show (5 / 3 - 2 : ℝ) = -1 / 3 by norm_num] using hd

lemma tfPowerDerivative_bound (a b t : ℝ) (ht : |t| ≤ 1) :
    ‖tfPowerDerivative (a + t * b) * b‖ ≤
      (5 / 3 : ℝ) * (|a| + |b|) ^ (5 / 3 : ℝ) := by
  have hs : 0 ≤ |a| + |b| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hh : |a + t * b| ≤ |a| + |b| := by
    calc
      _ ≤ |a| + |t * b| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right ht (abs_nonneg b)]
  rw [Real.norm_eq_abs, abs_mul, tfPowerDerivative_abs]
  have hp := Real.rpow_le_rpow (abs_nonneg _) hh (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hS : (|a| + |b|) ^ (5 / 3 : ℝ) = (|a| + |b|) ^ (2 / 3 : ℝ) * (|a| + |b|) := by
    rw [show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num,
      Real.rpow_add_of_nonneg hs (by norm_num) (by norm_num), Real.rpow_one]
  rw [hS]
  nlinarith [mul_le_mul hp (show |b| ≤ |a| + |b| by linarith [abs_nonneg a])
    (abs_nonneg b) (Real.rpow_nonneg hs (2 / 3 : ℝ))]

end CoulombAnalysis

end

end OAI
