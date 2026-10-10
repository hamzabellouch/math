import Mathlib
import OAI.Geometry.BallPacking.Holder.NonlinearCR

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Filter MeasureTheory

lemma smoothCauchyKernel_second_directional {δ : ℝ} (hδ : 0 < δ) (z v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ (smoothCauchyKernel δ) y v) z w =
      (-(2 * inner ℝ z w) / (‖z‖ ^ 2 + δ) ^ 2) • star v -
      (2 * inner ℝ w v / (‖z‖ ^ 2 + δ) ^ 2 -
        8 * inner ℝ z v * inner ℝ z w / (‖z‖ ^ 2 + δ) ^ 3) • star z -
      (2 * inner ℝ z v / (‖z‖ ^ 2 + δ) ^ 2) • star w := by
  have hq : 0 < ‖z‖ ^ 2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hqi := (hasDerivAt_inv hq.ne').comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const δ)
  have hi : HasFDerivAt (fun y : ℂ => inner ℝ y v) (innerSL ℝ v) z := by
    convert! (innerSL ℝ v).hasFDerivAt using 1
    ext y
    simpa only [innerSL_apply_apply] using (real_inner_comm y v).symm
  have ht := (hi.const_mul 2).mul (hqi.pow 2)
  have hd := (hqi.smul_const (star v)).sub
    (ht.smul (starL ℝ : ℂ ≃L[ℝ] ℂ).hasFDerivAt)
  have he : (fun y => fderiv ℝ (smoothCauchyKernel δ) y v) =
      (fun y => (‖y‖ ^ 2 + δ)⁻¹ • star v -
        (2 * inner ℝ y v * ((‖y‖ ^ 2 + δ)⁻¹) ^ 2) • star y) := by
    funext y
    rw [smoothCauchyKernel_fderiv hδ, div_eq_mul_inv, inv_pow]
  rw [he]
  change HasFDerivAt (fun y : ℂ => (‖y‖ ^ 2 + δ)⁻¹ • star v -
      (2 * inner ℝ y v * ((‖y‖ ^ 2 + δ)⁻¹) ^ 2) • star y) _ z at hd
  rw [hd.fderiv]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, two_smul, smul_eq_mul, Function.comp_apply]
  simp only [Pi.mul_apply, Nat.reduceSub, pow_one, div_eq_mul_inv, inv_pow, ContinuousLinearEquiv.coe_coe]
  rw [real_inner_comm v w]
  change (-((‖z‖ ^ 2 + δ) ^ 2)⁻¹ * (inner ℝ z w + inner ℝ z w)) • star v -
      ((2 * inner ℝ z v * ((‖z‖ ^ 2 + δ) ^ 2)⁻¹) • star w +
        (2 * inner ℝ z v *
              (((‖z‖ ^ 2 + δ)⁻¹ + (‖z‖ ^ 2 + δ)⁻¹) *
                (-((‖z‖ ^ 2 + δ) ^ 2)⁻¹ * (inner ℝ z w + inner ℝ z w))) +
            ((‖z‖ ^ 2 + δ) ^ 2)⁻¹ * (inner ℝ v w + inner ℝ v w)) • star z) = _
  simp only [← inv_pow]
  module

lemma smoothCauchyKernel_second_norm {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : z ≠ 0) (v w : ℂ) :
    ‖fderiv ℝ (fun y => fderiv ℝ (smoothCauchyKernel δ) y v) z w‖ ≤
      (14 / ‖z‖^3) * ‖v‖ * ‖w‖ := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hq : 0 < ‖z‖^2+δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hq2 : ‖z‖^4 ≤ (‖z‖^2+δ)^2 := by
    calc
      _ = (‖z‖^2)^2 := by ring
      _ ≤ _ := by gcongr; linarith
  have hq3 : ‖z‖^6 ≤ (‖z‖^2+δ)^3 := by
    calc
      _ = (‖z‖^2)^3 := by ring
      _ ≤ _ := by gcongr; linarith
  rw [smoothCauchyKernel_second_directional hδ]
  calc
    _ ≤ ‖(-(2*inner ℝ z w)/(‖z‖^2+δ)^2) • star v‖ +
        ‖(2*inner ℝ w v/(‖z‖^2+δ)^2 -
          8*inner ℝ z v*inner ℝ z w/(‖z‖^2+δ)^3) • star z‖ +
        ‖(2*inner ℝ z v/(‖z‖^2+δ)^2) • star w‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (2*|inner ℝ z w|/(‖z‖^2+δ)^2)*‖v‖ +
        ((2*|inner ℝ w v|/(‖z‖^2+δ)^2) +
          (8*|inner ℝ z v| *|inner ℝ z w|/(‖z‖^2+δ)^3))*‖z‖ +
        (2*|inner ℝ z v|/(‖z‖^2+δ)^2)*‖w‖ := by
      simp only [norm_smul, norm_star, Real.norm_eq_abs, abs_div, abs_neg, abs_mul,
        abs_pow, abs_of_pos hq, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      gcongr
      apply (abs_sub _ _).trans_eq
      simp only [abs_div, abs_mul, abs_pow, abs_of_pos hq,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 8)]
    _ ≤ (2*(‖z‖*‖w‖)/‖z‖^4)*‖v‖ +
        ((2*(‖w‖*‖v‖)/‖z‖^4) +
          (8*(‖z‖*‖v‖)*(‖z‖*‖w‖)/‖z‖^6))*‖z‖ +
        (2*(‖z‖*‖v‖)/‖z‖^4)*‖w‖ := by
      gcongr <;> exact abs_real_inner_le_norm _ _
    _ = _ := by field_simp; ring


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_directional_eq {f : ℂ → E} (hf : ContDiff ℝ ∞ f) (z v w : ℂ) :
    fderiv ℝ (fun y => fderiv ℝ f y v) z w = fderiv ℝ (fderiv ℝ f) z w v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z)
    (differentiableAt_const v)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]

lemma norm_second_jet (f : ℂ → E) (z : ℂ) :
    ‖iteratedFDeriv ℝ 2 f z‖ = ‖fderiv ℝ (fderiv ℝ f) z‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

lemma second_directional_norm_le {f : ℂ → E} (hf : ContDiff ℝ ∞ f) (z v w : ℂ) :
    ‖fderiv ℝ (fun y => fderiv ℝ f y v) z w‖ ≤
      ‖iteratedFDeriv ℝ 2 f z‖ * ‖v‖ * ‖w‖ := by
  rw [second_directional_eq hf, norm_second_jet]
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  calc
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) z‖ * ‖w‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = _ := by ring

lemma norm_first_smul_le {b : ℂ → ℝ} {K : ℂ → E}
    (hb : ContDiff ℝ ∞ b) (hK : ContDiff ℝ ∞ K) (z : ℂ) :
    ‖fderiv ℝ (fun w => b w • K w) z‖ ≤
      ‖b z‖*‖fderiv ℝ K z‖ + ‖fderiv ℝ b z‖*‖K z‖ := by
  have he := norm_iteratedFDeriv_smul_le hb hK z (by simp : (1:ℕ) ≤ (∞ : ℕ∞ω))
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.sub_zero, Nat.sub_self, Nat.reduceSub, norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero] using he

lemma norm_second_smul_le {b : ℂ → ℝ} {K : ℂ → E}
    (hb : ContDiff ℝ ∞ b) (hK : ContDiff ℝ ∞ K) (z : ℂ) :
    ‖iteratedFDeriv ℝ 2 (fun w => b w • K w) z‖ ≤
      ‖b z‖*‖iteratedFDeriv ℝ 2 K z‖ +
        2*‖fderiv ℝ b z‖*‖fderiv ℝ K z‖ +
        ‖iteratedFDeriv ℝ 2 b z‖*‖K z‖ := by
  have he := norm_iteratedFDeriv_smul_le hb hK z (show (2:ℕ) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.cast_one, one_mul,
    Nat.sub_zero, Nat.sub_self, Nat.reduceSub, Nat.cast_ofNat,
    norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero] using he

lemma norm_first_rescale {f : ℂ → E} (hf : ContDiff ℝ ∞ f) {r : ℝ} (hr : 0 < r)
    (z : ℂ) : ‖fderiv ℝ (fun w => f (r⁻¹ • w)) z‖ =
      r⁻¹ * ‖fderiv ℝ f (r⁻¹ • z)‖ := by
  have he := congrArg (fun g => ‖g z‖)
    (iteratedFDeriv_comp_const_smul r⁻¹ (hf.of_le (by simp : (1:ℕ∞ω) ≤ ∞)))
  simpa only [norm_iteratedFDeriv_one, pow_one, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] using he

lemma norm_second_rescale {f : ℂ → E} (hf : ContDiff ℝ ∞ f) {r : ℝ} (_hr : 0 < r)
    (z : ℂ) : ‖iteratedFDeriv ℝ 2 (fun w => f (r⁻¹ • w)) z‖ =
      (r^2)⁻¹ * ‖iteratedFDeriv ℝ 2 f (r⁻¹ • z)‖ := by
  have he := congrArg (fun g => ‖g z‖)
    (iteratedFDeriv_comp_const_smul r⁻¹ (hf.of_le (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)))
  simpa only [norm_smul, inv_pow, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg r))] using he


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory

def schauderBump : ContDiffBump (0:ℂ) where
  rIn := 3/2
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def scaledSchauderBump (r : ℝ) (z : ℂ) : ℝ := schauderBump (r⁻¹ • z)

lemma scaledSchauderBump_smooth (r : ℝ) : ContDiff ℝ ∞ (scaledSchauderBump r) :=
  schauderBump.contDiff.comp (contDiff_id.const_smul r⁻¹)

lemma scaledSchauderBump_compact {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (scaledSchauderBump r) :=
  schauderBump.hasCompactSupport.comp_smul (inv_ne_zero hr.ne')

lemma scaledSchauderBump_range (r : ℝ) (z : ℂ) :
    scaledSchauderBump r z ∈ Icc (0:ℝ) 1 := ⟨schauderBump.nonneg, schauderBump.le_one⟩

lemma scaledSchauderBump_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (scaledSchauderBump r) ⊆ Metric.closedBall (0:ℂ) (2*r) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hz' : r⁻¹ • z ∈ Function.support schauderBump := hz
  rw [schauderBump.support_eq] at hz'
  simp only [Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at hz'
  change r⁻¹ * ‖z‖ < 2 at hz'
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [inv_mul_eq_div, div_lt_iff₀ hr] at hz'
  exact hz'.le

lemma scaledSchauderBump_eventually_one {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ ≤ r) : scaledSchauderBump r =ᶠ[𝓝 z] (fun _ => 1) := by
  have ht : r⁻¹ • z ∈ Metric.ball (0:ℂ) schauderBump.rIn := by
    simp only [Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    change r⁻¹ * ‖z‖ < 3/2
    have : r⁻¹ * ‖z‖ ≤ 1 := by rwa [inv_mul_eq_div, div_le_one hr]
    linarith
  exact (schauderBump.eventuallyEq_one_of_mem_ball ht).comp_tendsto
    ((continuous_id.const_smul r⁻¹).tendsto z)

lemma scaledSchauderBump_homogeneous_bounds :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : ℝ, 0 < r → ∀ z : ℂ, z ≠ 0 →
      ‖fderiv ℝ (scaledSchauderBump r) z‖ ≤ 2*M/‖z‖ ∧
      ‖iteratedFDeriv ℝ 2 (scaledSchauderBump r) z‖ ≤ 4*M/‖z‖^2 := by
  obtain ⟨M,hM,h0,h1,h2,h3⟩ :=
    (HolderCompletion.boundedCThree_of_compactSupport schauderBump.contDiff
      schauderBump.hasCompactSupport).bounded
  refine ⟨M,hM,?_⟩
  intro r hr z hz
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  by_cases ht : z ∈ tsupport (scaledSchauderBump r)
  · have hz2 : ‖z‖ ≤ 2*r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using scaledSchauderBump_tsupport hr ht
    constructor
    · change ‖fderiv ℝ (fun w => schauderBump (r⁻¹ • w)) z‖ ≤ _
      rw [norm_first_rescale schauderBump.contDiff hr]
      calc
        _ ≤ r⁻¹*M := mul_le_mul_of_nonneg_left (h1 _) (inv_nonneg.mpr hr.le)
        _ ≤ _ := by rw [inv_mul_eq_div, div_le_div_iff₀ hr hp]; nlinarith
    · change ‖iteratedFDeriv ℝ 2 (fun w => schauderBump (r⁻¹ • w)) z‖ ≤ _
      rw [norm_second_rescale schauderBump.contDiff hr]
      calc
        _ ≤ (r^2)⁻¹*M := mul_le_mul_of_nonneg_left (by rw [norm_second_jet]; exact h2 _)
          (inv_nonneg.mpr (sq_nonneg r))
        _ ≤ _ := by
          rw [inv_mul_eq_div, div_le_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos hp)]
          have : ‖z‖^2 ≤ 4*r^2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left this hM]
  · have hd : fderiv ℝ (scaledSchauderBump r) z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) ht
    have hd2 : iteratedFDeriv ℝ 2 (scaledSchauderBump r) z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => ht (tsupport_iteratedFDeriv_subset 2 h)
    simp only [hd, hd2, norm_zero]
    constructor <;> positivity



lemma smoothCauchyKernel_first_opNorm {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ≠ 0) :
    ‖fderiv ℝ (smoothCauchyKernel δ) z‖ ≤ 3/‖z‖^2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (smoothCauchyKernel_fderiv_norm hδ hz)

lemma smoothCauchyKernel_second_opNorm {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ 2 (smoothCauchyKernel δ) z‖ ≤ 14/‖z‖^3 := by
  rw [norm_second_jet]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [← second_directional_eq (smoothCauchyKernel_smooth hδ)]
  convert! smoothCauchyKernel_second_norm hδ hz v w using 1; ring

lemma cutoff_smoothCauchyKernel_jet_bounds (b : ContDiffBump (0:ℂ)) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ δ : ℝ, 0 < δ → ∀ z : ℂ, z ≠ 0 →
      ‖b z • smoothCauchyKernel δ z‖ ≤ ‖z‖⁻¹ ∧
      ‖fderiv ℝ (fun w => b w • smoothCauchyKernel δ w) z‖ ≤ C₁/‖z‖^2 ∧
      ‖iteratedFDeriv ℝ 2 (fun w => b w • smoothCauchyKernel δ w) z‖ ≤ C₂/‖z‖^3 := by
  obtain ⟨M,hM,h0,h1,h2,h3⟩ :=
    (HolderCompletion.boundedCThree_of_compactSupport b.contDiff b.hasCompactSupport).bounded
  have hR := b.rOut_pos
  refine ⟨M*b.rOut+3, M*b.rOut^2+6*M*b.rOut+14, by positivity, by positivity, ?_⟩
  intro δ hδ z hz
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hbn : ‖b z‖ ≤ 1 := by simpa only [Real.norm_of_nonneg b.nonneg] using b.le_one
  refine ⟨?_, ?_⟩
  · rw [norm_smul]
    exact (mul_le_mul hbn (smoothCauchyKernel_norm hδ z) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  by_cases ht : z ∈ tsupport (fun w => b w • smoothCauchyKernel δ w)
  · have ht' : ‖z‖ ≤ b.rOut := by
      have := tsupport_smul_subset_left b (smoothCauchyKernel δ) ht
      simpa only [b.tsupport_eq, Metric.mem_closedBall, dist_zero_right] using this
    constructor
    · calc
        _ ≤ ‖b z‖*‖fderiv ℝ (smoothCauchyKernel δ) z‖ +
            ‖fderiv ℝ b z‖*‖smoothCauchyKernel δ z‖ :=
          norm_first_smul_le b.contDiff (smoothCauchyKernel_smooth hδ) z
        _ ≤ 1*(3/‖z‖^2) + M*‖z‖⁻¹ := by
          exact add_le_add (mul_le_mul hbn (smoothCauchyKernel_first_opNorm hδ hz)
            (norm_nonneg _) zero_le_one) (mul_le_mul (h1 z)
            (smoothCauchyKernel_norm hδ z) (norm_nonneg _) hM)
        _ = (3+M*‖z‖)/‖z‖^2 := by field_simp
        _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          nlinarith [mul_le_mul_of_nonneg_left ht' hM]
    · calc
        _ ≤ ‖b z‖*‖iteratedFDeriv ℝ 2 (smoothCauchyKernel δ) z‖ +
            2*‖fderiv ℝ b z‖*‖fderiv ℝ (smoothCauchyKernel δ) z‖ +
            ‖iteratedFDeriv ℝ 2 b z‖*‖smoothCauchyKernel δ z‖ :=
          norm_second_smul_le b.contDiff (smoothCauchyKernel_smooth hδ) z
        _ ≤ 1*(14/‖z‖^3) + 2*M*(3/‖z‖^2) + M*‖z‖⁻¹ := by
          apply add_le_add _ (mul_le_mul (by rw [norm_second_jet]; exact h2 z)
            (smoothCauchyKernel_norm hδ z) (norm_nonneg _) hM)
          exact add_le_add (mul_le_mul hbn (smoothCauchyKernel_second_opNorm hδ hz)
            (norm_nonneg _) zero_le_one) (mul_le_mul
            (mul_le_mul_of_nonneg_left (h1 z) (by norm_num))
            (smoothCauchyKernel_first_opNorm hδ hz) (norm_nonneg _) (by positivity))
        _ = (14+6*M*‖z‖+M*‖z‖^2)/‖z‖^3 := by field_simp; ring
        _ ≤ _ := by
          have hh : ‖z‖^2 ≤ b.rOut^2 := by nlinarith [b.rOut_pos]
          have ha := mul_le_mul_of_nonneg_left ht' (show 0 ≤ 6*M from by positivity)
          have hb := mul_le_mul_of_nonneg_left hh hM
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  · have hdz := fderiv_of_notMem_tsupport (𝕜 := ℝ) ht
    have hd2 : iteratedFDeriv ℝ 2 (fun w => b w • smoothCauchyKernel δ w) z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun h => ht (tsupport_iteratedFDeriv_subset 2 h)
    simp only [hdz, hd2, norm_zero]
    constructor <;> positivity


end
section
open scoped Topology
open Set Filter MeasureTheory

def schauderNearWeight (z : ℂ) : ℝ :=
  (Metric.closedBall (0:ℂ) 2).indicator (fun w => ‖w‖ ^ (-(5:ℝ)/3)) z

def schauderFarWeight (z : ℂ) : ℝ :=
  (Ioi (1:ℝ)).indicator (fun r => r ^ (-(8:ℝ)/3)) ‖z‖

lemma schauderNearWeight_nonneg (z : ℂ) : 0 ≤ schauderNearWeight z := by
  exact indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg w) _) z

lemma schauderFarWeight_nonneg (z : ℂ) : 0 ≤ schauderFarWeight z := by
  apply indicator_nonneg _ ‖z‖
  intro r hr
  exact Real.rpow_nonneg (zero_le_one.trans hr.le) _

lemma schauderNearWeight_integrable : Integrable schauderNearWeight := by
  apply IntegrableOn.integrable_indicator _ measurableSet_closedBall
  apply LocallyIntegrable.integrableOn_isCompact _ (isCompact_closedBall _ _)
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := (5:ℝ)/3) (by simp) (by norm_num)
  · exact Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
      norm_num
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma schauderFarWeight_integrable : Integrable schauderFarWeight := by
  unfold schauderFarWeight
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)]
  have h : Integrable ((Ioi (1:ℝ)).indicator (fun r => r ^ (-(5:ℝ)/3))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(5:ℝ)/3 < -1) zero_lt_one).integrable_indicator
      measurableSet_Ioi
  apply h.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  by_cases h1 : 1 < r
  · rw [indicator_of_mem (show r ∈ Ioi (1:ℝ) from h1),
      indicator_of_mem (show r ∈ Ioi (1:ℝ) from h1)]
    have he := Real.rpow_add (show 0 < r from hr) (1:ℝ) (-(8:ℝ)/3)
    norm_num at he
    simpa only [neg_div] using he
  · simp only [indicator_of_notMem (show r ∉ Ioi (1:ℝ) from h1), mul_zero]

def scaledSchauderWeight (β : ℝ) (W : ℂ → ℝ) (r : ℝ) (z : ℂ) : ℝ :=
  r ^ β * W (r⁻¹ • z)

lemma scaledSchauderWeight_integrable {W : ℂ → ℝ} (hW : Integrable W)
    (β : ℝ) {r : ℝ} (hr : 0 < r) : Integrable (scaledSchauderWeight β W r) :=
  (hW.comp_smul (inv_ne_zero hr.ne')).const_mul _

lemma integral_scaledSchauderWeight (β : ℝ) (W : ℂ → ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ z, scaledSchauderWeight β W r z) = r ^ (β+2) * ∫ z, W z := by
  unfold scaledSchauderWeight
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume W hr.le]
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_two, ← Real.rpow_add hr]

lemma scaledNearWeight_value {r : ℝ} (hr : 0 < r) (z : ℂ) :
    scaledSchauderWeight (-(5:ℝ)/3) schauderNearWeight r z =
      (Metric.closedBall (0:ℂ) (2*r)).indicator (fun w => ‖w‖^(-(5:ℝ)/3)) z := by
  have hn : ‖r⁻¹ • z‖ = r⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hm : r⁻¹ • z ∈ Metric.closedBall (0:ℂ) 2 ↔ z ∈ Metric.closedBall (0:ℂ) (2*r) := by
    simp only [Metric.mem_closedBall, dist_zero_right, hn]
    rw [inv_mul_eq_div, div_le_iff₀ hr]
  simp only [scaledSchauderWeight, schauderNearWeight]
  by_cases hz : z ∈ Metric.closedBall (0:ℂ) (2*r)
  · rw [indicator_of_mem (hm.mpr hz), indicator_of_mem hz, hn,
      Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg z), Real.inv_rpow hr.le,
      ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne', one_mul]
  · rw [indicator_of_notMem (fun h => hz (hm.mp h)), indicator_of_notMem hz, mul_zero]

lemma scaledFarWeight_value {r : ℝ} (hr : 0 < r) (z : ℂ) :
    scaledSchauderWeight (-(8:ℝ)/3) schauderFarWeight r z =
      (Ioi r).indicator (fun t => t^(-(8:ℝ)/3)) ‖z‖ := by
  have hn : ‖r⁻¹ • z‖ = r⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  have hm : 1 < ‖r⁻¹ • z‖ ↔ r < ‖z‖ := by
    rw [hn, inv_mul_eq_div, lt_div_iff₀ hr, one_mul]
  simp only [scaledSchauderWeight, schauderFarWeight]
  by_cases hz : r < ‖z‖
  · rw [indicator_of_mem (show ‖r⁻¹ • z‖ ∈ Ioi (1:ℝ) from hm.mpr hz),
      indicator_of_mem (show ‖z‖ ∈ Ioi r from hz), hn,
      Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg z), Real.inv_rpow hr.le,
      ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne', one_mul]
  · rw [indicator_of_notMem (show ‖r⁻¹ • z‖ ∉ Ioi (1:ℝ) from fun h => hz (hm.mp h)),
      indicator_of_notMem (show ‖z‖ ∉ Ioi r from hz), mul_zero]


end
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma compact_kernel_convolution_direction {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      convolution (fun w => fderiv ℝ K w v) g (ContinuousLinearMap.lsmul ℝ ℂ) volume x := by
  rw [compact_kernel_convolution_fderiv hK hc hg]
  rfl

lemma compact_kernel_convolution_derivative_lipschitz {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {W : ℂ → ℝ} (hW : Integrable W) (hW0 : ∀ w, 0 ≤ W w)
    (hb : ∀ x w v t : ℂ,
      ‖fderiv ℝ (fun y => fderiv ℝ K y v) w t‖ * ‖g (x-w)-g x‖ ≤
        W w * ‖v‖ * ‖t‖) (x y : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
        fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
      (∫ w, W w) * ‖x-y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (integral_nonneg hW0) (norm_nonneg _))
  intro v
  simp only [sub_apply, compact_kernel_convolution_direction hK hc hg]
  have hKv : ContDiff ℝ ∞ (fun w => fderiv ℝ K w v) :=
    (hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcKv : HasCompactSupport (fun w => fderiv ℝ K w v) := hc.fderiv_apply (𝕜 := ℝ) v
  have hMv (z : ℂ) :
      ‖fderiv ℝ (convolution (fun w => fderiv ℝ K w v) g
        (ContinuousLinearMap.lsmul ℝ ℂ) volume) z‖ ≤ (∫ w, W w) * ‖v‖ := by
    have he := compact_kernel_convolution_derivative_bound hKv hcKv hg (hW.mul_const ‖v‖)
      (fun a w t => hb a w v t) z
    simpa only [integral_mul_const] using he
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (s := (univ : Set ℂ))
    (fun z _ => (hcKv.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℂ)
      (hKv.of_le (by simp)) hg.locallyIntegrable z).differentiableAt)
    (fun z _ => hMv z) convex_univ (mem_univ y) (mem_univ x)
  convert! he using 1
  ring

omit [CompleteSpace E] in
lemma compact_convolution_split_fderiv {K N F : ℂ → ℂ}
    (hN : ContDiff ℝ ∞ N) (hcN : HasCompactSupport N)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hKF : ∀ w, K w = N w + F w) {g : ℂ → E} (hg : Continuous g) (x : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x =
      fderiv ℝ (convolution N g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x +
      fderiv ℝ (convolution F g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x := by
  have he : convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume =
      convolution N g (ContinuousLinearMap.lsmul ℝ ℂ) volume +
      convolution F g (ContinuousLinearMap.lsmul ℝ ℂ) volume := by
    funext z
    simp only [convolution, hKF, ContinuousLinearMap.map_add, add_apply, Pi.add_apply]
    exact integral_add
      (hcN.convolutionExists_left _ hN.continuous hg.locallyIntegrable z)
      (hcF.convolutionExists_left _ hF.continuous hg.locallyIntegrable z)
  rw [he]
  exact fderiv_add
    (hcN.hasFDerivAt_convolution_left _ (hN.of_le (by simp)) hg.locallyIntegrable x).differentiableAt
    (hcF.hasFDerivAt_convolution_left _ (hF.of_le (by simp)) hg.locallyIntegrable x).differentiableAt

lemma compact_convolution_split_derivative_bound {K N F : ℂ → ℂ}
    (hN : ContDiff ℝ ∞ N) (hcN : HasCompactSupport N)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    (hKF : ∀ w, K w = N w + F w) {g : ℂ → E} (hg : Continuous g)
    {WN WF : ℂ → ℝ} (hWN : Integrable WN) (hWF : Integrable WF)
    (hWF0 : ∀ w, 0 ≤ WF w)
    (hbN : ∀ x w v : ℂ, ‖fderiv ℝ N w v‖ * ‖g (x-w)-g x‖ ≤ WN w * ‖v‖)
    (hbF : ∀ x w v t : ℂ,
      ‖fderiv ℝ (fun y => fderiv ℝ F y v) w t‖ * ‖g (x-w)-g x‖ ≤
        WF w * ‖v‖ * ‖t‖) (x y : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x -
        fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) y‖ ≤
      2*(∫ w, WN w) + (∫ w, WF w)*‖x-y‖ := by
  rw [compact_convolution_split_fderiv hN hcN hF hcF hKF hg x,
    compact_convolution_split_fderiv hN hcN hF hcF hKF hg y]
  have hbr := compact_kernel_convolution_derivative_lipschitz hF hcF hg hWF hWF0 hbF x y
  have hx := compact_kernel_convolution_derivative_bound hN hcN hg hWN hbN x
  have hy := compact_kernel_convolution_derivative_bound hN hcN hg hWN hbN y
  have halg {A B C D : ℂ →L[ℝ] E} : ‖(A+B)-(C+D)‖ ≤ ‖A‖+‖C‖+‖B-D‖ := by
    calc
      _ = ‖(A-C)+(B-D)‖ := by congr 1; abel
      _ ≤ ‖A-C‖+‖B-D‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_sub_le A C) le_rfl
  exact halg.trans (by linarith)



end HigherDimensionalBallPacking.Rigidity
end

end OAI
