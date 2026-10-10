import Mathlib
import OAI.Probability.LogConcave.Analysis.GaussianCoefficient
import OAI.Probability.LogConcave.Numerics.Remainder

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
namespace EulerDefect
open scoped RealInnerProductSpace Topology
open Asymptotics

variable {d : ℕ} {H : Point d → ℝ}

def proposalLog (H : Point d → ℝ) (h : ℝ) (x y : Point d) : ℝ :=
  -H x-‖y-x+h • gradient H x‖^2/(4*h)

def proposal (H : Point d → ℝ) (s : ℝ) (x z : Point d) : Point d :=
  x-s^2 • gradient H x+(Real.sqrt 2*s) • z

lemma log_ratio (h : ℝ) (hh : h ≠ 0) (x y : Point d) :
    proposalLog H h x y-proposalLog H h y x =
      Trapezoid.remainder H x y+h/4*(‖gradient H y‖^2-‖gradient H x‖^2) := by
  have he : x-y = -(y-x) := by abel
  simp only [proposalLog,Trapezoid.remainder,he,norm_add_sq_real,norm_neg,norm_smul,
    Real.norm_eq_abs,real_inner_smul_right,inner_neg_left,inner_add_right,mul_pow,sq_abs]
  field_simp
  ring

lemma proposal_displacement (s : ℝ) (x z : Point d) :
    proposal H s x z-x = -s^2 • gradient H x+(Real.sqrt 2*s) • z := by
  dsimp [proposal]
  simp only [neg_smul]
  abel

lemma proposal_zero (x z : Point d) : proposal H 0 x z = x := by simp [proposal]

lemma differentiable_proposal (x z : Point d) : Differentiable ℝ (fun s => proposal H s x z) := by
  unfold proposal
  fun_prop

lemma continuous_proposal (x z : Point d) : Continuous (fun s => proposal H s x z) :=
  (differentiable_proposal x z).continuous

lemma remainder_scaled_tendsto (hH : ContDiff ℝ 2 H) (x z : Point d) :
    Filter.Tendsto (fun s => Trapezoid.remainder H x (proposal H s x z)/s^2) (𝓝 0) (𝓝 0) := by
  have ht : Filter.Tendsto (fun s => proposal H s x z) (𝓝 0) (𝓝 x) := by
    simpa only [proposal_zero] using (continuous_proposal (H := H) x z).tendsto 0
  have hl := (Trapezoid.remainder_littleO hH x).comp_tendsto ht
  have hb := (differentiable_proposal (H := H) x z 0).hasDerivAt.isBigO_sub.norm_left.pow 2
  simp only [proposal_zero,sub_zero] at hb
  exact (hl.trans_isBigO hb).tendsto_div_nhds_zero

lemma scaled_log_ratio (s : ℝ) (x z : Point d) :
    (proposalLog H (s^2) x (proposal H s x z)-
      proposalLog H (s^2) (proposal H s x z) x)/s^2 =
    Trapezoid.remainder H x (proposal H s x z)/s^2+
      (‖gradient H (proposal H s x z)‖^2-‖gradient H x‖^2)/4 := by
  by_cases hs : s = 0
  · subst s; simp [proposal_zero]
  rw [log_ratio (s^2) (pow_ne_zero _ hs)]
  field_simp

theorem scaled_log_ratio_tendsto (hH : ContDiff ℝ 2 H) (x z : Point d) :
    Filter.Tendsto (fun s =>
      (proposalLog H (s^2) x (proposal H s x z)-
        proposalLog H (s^2) (proposal H s x z) x)/s^2) (𝓝 0) (𝓝 0) := by
  simp_rw [scaled_log_ratio]
  have ht : Filter.Tendsto (fun s => proposal H s x z) (𝓝 0) (𝓝 x) := by
    simpa only [proposal_zero] using (continuous_proposal (H := H) x z).tendsto 0
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hn := ((hg.tendsto x).comp ht).norm.pow 2
  have hdiff := (hn.sub_const (‖gradient H x‖^2)).div_const 4
  simpa only [sub_self,zero_div,add_zero,Function.comp_apply] using
    (remainder_scaled_tendsto hH x z).add hdiff

lemma displacement_bound {s : ℝ} (hs : |s| ≤ 1) (x z : Point d) :
    ‖proposal H s x z-x‖ ≤ |s| *(‖gradient H x‖+Real.sqrt 2*‖z‖) := by
  rw [proposal_displacement]
  have ht := norm_add_le (-s^2 • gradient H x) ((Real.sqrt 2*s) • z)
  simp only [norm_smul,Real.norm_eq_abs,abs_neg,abs_pow,abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg 2)] at ht
  have hh : |s|^2 ≤ |s| := by nlinarith [abs_nonneg s]
  have hb := mul_le_mul_of_nonneg_right hh (norm_nonneg (gradient H x))
  nlinarith only [ht,hb]

lemma gradient_norm_sq_difference_bound {M : ℝ≥0} (hM : LipschitzWith M (gradient H))
    (x y : Point d) :
    |‖gradient H y‖^2-‖gradient H x‖^2| ≤
      (M:ℝ)*‖y-x‖*(2*‖gradient H x‖+(M:ℝ)*‖y-x‖) := by
  have hd := hM.norm_sub_le y x
  have hn := norm_sub_norm_le (gradient H y) (gradient H x)
  have hab := abs_norm_sub_norm_le (gradient H y) (gradient H x)
  have hgy : ‖gradient H y‖ ≤ ‖gradient H x‖+(M:ℝ)*‖y-x‖ := by linarith
  have he : ‖gradient H y‖^2-‖gradient H x‖^2 =
      (‖gradient H y‖-‖gradient H x‖)*(‖gradient H y‖+‖gradient H x‖) := by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ ‖gradient H y‖+‖gradient H x‖)]
  exact mul_le_mul (hab.trans hd) (by linarith) (by positivity) (by positivity)

lemma scaled_log_ratio_bound (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) {s : ℝ} (hs : |s| ≤ 1) (x z : Point d) :
    |(proposalLog H (s^2) x (proposal H s x z)-
      proposalLog H (s^2) (proposal H s x z) x)/s^2| ≤
    (M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖)^2+
      (M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖)*
        (2*‖gradient H x‖+(M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖))/4 := by
  rw [scaled_log_ratio]
  let A := ‖gradient H x‖+Real.sqrt 2*‖z‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd := displacement_bound (H := H) hs x z
  have hdA : ‖proposal H s x z-x‖ ≤ A :=
    hd.trans (by exact mul_le_of_le_one_left hA hs)
  have hterm : |Trapezoid.remainder H x (proposal H s x z)/s^2| ≤ (M:ℝ)*A^2 := by
    by_cases hs0 : s = 0
    · simp [hs0]; positivity
    rw [abs_div,abs_of_nonneg (sq_nonneg s)]
    apply (div_le_iff₀ (sq_pos_of_ne_zero hs0)).mpr
    have hb := Trapezoid.remainder_bound hH hM x (proposal H s x z)
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) M.coe_nonneg
    rw [mul_pow,sq_abs] at hh
    dsimp [A] at *
    nlinarith only [hb,hh]
  have hg := gradient_norm_sq_difference_bound hM x (proposal H s x z)
  have hmul : (M:ℝ)*‖proposal H s x z-x‖*(2*‖gradient H x‖+(M:ℝ)*‖proposal H s x z-x‖) ≤
      (M:ℝ)*A*(2*‖gradient H x‖+(M:ℝ)*A) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hdA M.coe_nonneg
    · linarith [mul_le_mul_of_nonneg_left hdA M.coe_nonneg]
    · positivity
    · positivity
  have ht := abs_add_le (Trapezoid.remainder H x (proposal H s x z)/s^2)
    ((‖gradient H (proposal H s x z)‖^2-‖gradient H x‖^2)/4)
  apply ht.trans
  apply add_le_add hterm
  simpa only [abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)] using
    div_le_div_of_nonneg_right (hg.trans hmul) (by norm_num : (0:ℝ) ≤ 4)

lemma quadratic_dominator_bound (M : ℝ≥0) (x z : Point d) :
    (M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖)^2+
      (M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖)*
        (2*‖gradient H x‖+(M:ℝ)*(‖gradient H x‖+Real.sqrt 2*‖z‖))/4 ≤
    (6*(M:ℝ)+M^2)*(‖gradient H x‖^2+‖z‖^2) := by
  let A := ‖gradient H x‖+Real.sqrt 2*‖z‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hg : ‖gradient H x‖ ≤ A := by
    exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hs : A^2 ≤ 4*(‖gradient H x‖^2+‖z‖^2) := by
    dsimp [A]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      sq_nonneg (‖gradient H x‖-Real.sqrt 2*‖z‖),sq_nonneg ‖gradient H x‖]
  have hh : (M:ℝ)*A*‖gradient H x‖ ≤ (M:ℝ)*A^2 := by
    simpa only [pow_two,mul_assoc] using mul_le_mul_of_nonneg_left hg (mul_nonneg M.coe_nonneg hA)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (M:ℝ)+(M:ℝ)/2+(M:ℝ)^2/4 by positivity)
  change (M:ℝ)*A^2+(M:ℝ)*A*(2*‖gradient H x‖+(M:ℝ)*A)/4 ≤ _
  nlinarith only [hh,hm]

open MeasureTheory ProbabilityTheory in

theorem expected_scaled_log_ratio_tendsto (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (hi : Integrable (fun x => ‖gradient H x‖^2) μ) :
    Filter.Tendsto (fun s => ∫ p : Point d × Point d,
      |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
        proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|
      ∂μ.prod (stdGaussian (Point d))) (𝓝 0) (𝓝 0) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hz : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (Point d))).norm.integrable_sq
  have hb := ((hi.comp_fst (stdGaussian (Point d))).add (hz.comp_snd μ)).const_mul
    (6*(M:ℝ)+(M:ℝ)^2)
  have hh := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.prod (stdGaussian (Point d))) (l := 𝓝 (0:ℝ))
    (f := fun _ => (0:ℝ))
    (fun p : Point d × Point d => (6*(M:ℝ)+(M:ℝ)^2)*(‖gradient H p.1‖^2+‖p.2‖^2))
    (F := fun s p => |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
      proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|) ?_ ?_ hb ?_
  · simpa only [integral_zero] using hh
  · apply Filter.Eventually.of_forall
    intro s
    have hcont : Continuous (fun p : Point d × Point d =>
        |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
          proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|) := by
      unfold proposalLog proposal
      fun_prop
    exact hcont.aestronglyMeasurable
  · have hs : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ 1 := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with s hs
      have hh : |s| < 1 := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hs
      exact hh.le
    filter_upwards [hs] with s hs
    filter_upwards [] with p
    rw [Real.norm_eq_abs,abs_abs]
    exact (scaled_log_ratio_bound hH hM hs p.1 p.2).trans (quadratic_dominator_bound M p.1 p.2)
  · filter_upwards [] with p
    simpa only [abs_zero] using (scaled_log_ratio_tendsto hH p.1 p.2).abs

end EulerDefect
end LogConcaveSampling

namespace LogConcaveSampling
namespace MetropolisBalance

lemma exp_gap (a b : ℝ) :
    |Real.exp a-Real.exp b| ≤ (Real.exp a+Real.exp b)*|a-b| := by
  wlog hab : b ≤ a generalizing a b
  · simpa only [abs_sub_comm,add_comm] using this b a (le_of_not_ge hab)
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab)),
    abs_of_nonneg (sub_nonneg.mpr hab)]
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b-a)) (Real.exp_pos a).le
  have he : Real.exp a*Real.exp (b-a) = Real.exp b := by rw [← Real.exp_add]; ring_nf
  rw [he] at hh
  nlinarith [mul_nonneg (Real.exp_pos b).le (sub_nonneg.mpr hab)]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

def defectWeight (H : Ω × Ω → ℝ) (p : Ω × Ω) : ℝ :=
  Real.exp (H p)*|H p-H p.swap|

lemma reverse_defect_integrable {H : Ω × Ω → ℝ}
    (hi : Integrable (defectWeight H) (μ.prod μ)) :
    Integrable (fun p => Real.exp (H p.swap)*|H p-H p.swap|) (μ.prod μ) := by
  convert! hi.swap using 1
  funext p
  simp only [defectWeight,Function.comp_apply,Prod.swap_swap,abs_sub_comm]

lemma integral_reverse_defect {H : Ω × Ω → ℝ} :
    (∫ p, Real.exp (H p.swap)*|H p-H p.swap| ∂μ.prod μ) =
      ∫ p, defectWeight H p ∂μ.prod μ := by
  have he : (fun p : Ω × Ω => Real.exp (H p.swap)*|H p-H p.swap|) =
      fun p => defectWeight H p.swap := by
    funext p
    simp only [defectWeight,Prod.swap_swap,abs_sub_comm]
  rw [he,integral_prod_swap]

lemma density_gap_integrable {H : Ω × Ω → ℝ} (hm : Measurable H)
    (hi : Integrable (defectWeight H) (μ.prod μ)) :
    Integrable (fun p => |Real.exp (H p)-Real.exp (H p.swap)|) (μ.prod μ) := by
  refine (hi.add (reverse_defect_integrable μ hi)).mono' (by fun_prop) ?_
  filter_upwards [] with p
  rw [Real.norm_eq_abs,abs_abs]
  have hh := exp_gap (H p) (H p.swap)
  dsimp [defectWeight]
  nlinarith only [hh]

lemma density_gap_bound {H : Ω × Ω → ℝ} (hm : Measurable H)
    (hi : Integrable (defectWeight H) (μ.prod μ)) :
    (∫ p, |Real.exp (H p)-Real.exp (H p.swap)| ∂μ.prod μ) ≤
      2*∫ p, defectWeight H p ∂μ.prod μ := by
  have hrev := reverse_defect_integrable μ hi
  have hb : (∫ p, |Real.exp (H p)-Real.exp (H p.swap)| ∂μ.prod μ) ≤
      ∫ p, defectWeight H p+Real.exp (H p.swap)*|H p-H p.swap| ∂μ.prod μ := by
    apply integral_mono (density_gap_integrable μ hm hi) (hi.add hrev)
    intro p
    dsimp [defectWeight]
    nlinarith only [exp_gap (H p) (H p.swap)]
  rw [integral_add hi hrev,integral_reverse_defect] at hb
  linarith only [hb]

omit [SFinite μ] in
lemma weighted_bounded_integrable {H : Ω × Ω → ℝ} (hm : Measurable H)
    (hi : Integrable (fun p => Real.exp (H p)) (μ.prod μ))
    {f : Ω × Ω → ℝ} (hf : Measurable f) {B : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ p, |f p| ≤ B) :
    Integrable (fun p => Real.exp (H p)*f p) (μ.prod μ) := by
  refine (hi.mul_const B).mono' (by fun_prop) ?_
  filter_upwards [] with p
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb p) (Real.exp_pos _).le

theorem one_step_defect {H : Ω × Ω → ℝ} (hm : Measurable H)
    (hi : Integrable (fun p => Real.exp (H p)) (μ.prod μ))
    (hR : Integrable (defectWeight H) (μ.prod μ))
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) :
    |(∫ p : Ω × Ω, Real.exp (H p)*f p.2 ∂μ.prod μ)-
      ∫ p : Ω × Ω, Real.exp (H p)*f p.1 ∂μ.prod μ| ≤
      2*B*∫ p, defectWeight H p ∂μ.prod μ := by
  have h₁ : Integrable (fun p : Ω × Ω => Real.exp (H p)*f p.2) (μ.prod μ) :=
    weighted_bounded_integrable μ hm hi (hf.comp measurable_snd) hB (fun p => hb p.2)
  have h₂ : Integrable (fun p : Ω × Ω => Real.exp (H p.swap)*f p.2) (μ.prod μ) :=
    weighted_bounded_integrable μ (hm.comp measurable_swap) hi.swap
      (hf.comp measurable_snd) hB (fun p => hb p.2)
  have he : (∫ p : Ω × Ω, Real.exp (H p)*f p.1 ∂μ.prod μ) =
      ∫ p : Ω × Ω, Real.exp (H p.swap)*f p.2 ∂μ.prod μ := by
    rw [← integral_prod_swap (fun p : Ω × Ω => Real.exp (H p)*f p.1)]
    rfl
  rw [he,← integral_sub h₁ h₂]
  have hd := density_gap_integrable μ hm hR
  have hn : (∫ p : Ω × Ω, |Real.exp (H p)*f p.2-Real.exp (H p.swap)*f p.2| ∂μ.prod μ) ≤
      B*∫ p, |Real.exp (H p)-Real.exp (H p.swap)| ∂μ.prod μ := by
    rw [← integral_const_mul]
    apply integral_mono (h₁.sub h₂).abs (hd.const_mul B)
    intro p
    change |Real.exp (H p)*f p.2-Real.exp (H p.swap)*f p.2| ≤
      B*|Real.exp (H p)-Real.exp (H p.swap)|
    rw [← sub_mul,abs_mul]
    exact mul_le_mul (le_refl _) (hb p.2) (abs_nonneg _) (abs_nonneg _) |>.trans_eq (mul_comm _ _)
  have hh := norm_integral_le_integral_norm
    (fun p : Ω × Ω => Real.exp (H p)*f p.2-Real.exp (H p.swap)*f p.2) (μ := μ.prod μ)
  simp only [Real.norm_eq_abs] at hh
  have hg := mul_le_mul_of_nonneg_left (density_gap_bound μ hm hR) hB
  nlinarith only [hh,hn,hg]

end MetropolisBalance
end LogConcaveSampling

namespace LogConcaveSampling
namespace MetropolisBalance
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

def densityLaw (c : ℝ≥0∞) (H : Ω × Ω → ℝ) : Measure (Ω × Ω) :=
  c • (μ.prod μ).withDensity (fun p => ENNReal.ofReal (Real.exp (H p)))

omit [SFinite μ] in
lemma densityLaw_integral {H : Ω × Ω → ℝ} (hm : Measurable H) (c : ℝ≥0∞)
    (f : Ω × Ω → ℝ) :
    (∫ p, f p ∂densityLaw μ c H) = c.toReal*∫ p, Real.exp (H p)*f p ∂μ.prod μ := by
  rw [densityLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]

omit [SFinite μ] in
lemma densityLaw_integrable {H : Ω × Ω → ℝ} (hm : Measurable H) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hct : c ≠ ⊤) (f : Ω × Ω → ℝ) :
    Integrable f (densityLaw μ c H) ↔ Integrable (fun p => Real.exp (H p)*f p) (μ.prod μ) := by
  rw [densityLaw,integrable_smul_measure hc hct,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]

theorem probability_one_step_defect {H : Ω × Ω → ℝ} (hm : Measurable H) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hct : c ≠ ⊤) [IsFiniteMeasure (densityLaw μ c H)]
    (hR : Integrable (fun p => |H p-H p.swap|) (densityLaw μ c H))
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) :
    |(∫ p : Ω × Ω, f p.2 ∂densityLaw μ c H)-
      ∫ p : Ω × Ω, f p.1 ∂densityLaw μ c H| ≤
      2*B*∫ p, |H p-H p.swap| ∂densityLaw μ c H := by
  have hi := (densityLaw_integrable μ hm hc hct (fun _ => 1)).mp (integrable_const 1)
  simp only [mul_one] at hi
  have hr := (densityLaw_integrable μ hm hc hct (fun p => |H p-H p.swap|)).mp hR
  have hh := one_step_defect μ hm hi hr hf hB hb
  rw [densityLaw_integral μ hm,densityLaw_integral μ hm,densityLaw_integral μ hm,
    ← mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
  have hh' := mul_le_mul_of_nonneg_left hh (ENNReal.toReal_nonneg (a := c))
  dsimp [defectWeight] at hh'
  nlinarith only [hh']

end MetropolisBalance
namespace EulerDefect
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {d : ℕ} {H : Point d → ℝ}

def joint (H : Point d → ℝ) (s : ℝ) : Measure (Point d × Point d) :=
  ((gibbs H).prod (stdGaussian (Point d))).map (fun p => (p.1,proposal H s p.1 p.2))

def jointCoefficient (H : Point d → ℝ) (s : ℝ) : ℝ≥0∞ :=
  (partition H)⁻¹*EulerDensity.noiseCoefficient d (Real.sqrt 2*s)

lemma joint_density (hH : ContDiff ℝ 2 H) {s : ℝ} (hs : s ≠ 0) :
    joint H s = MetropolisBalance.densityLaw volume (jointCoefficient H s)
      (fun p => proposalLog H (s^2) p.1 p.2) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous.measurable
  have he := EulerDensity.joint_density hH.continuous.measurable
    (fun x => x-s^2 • gradient H x) (by fun_prop)
    (mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)) hs)
  change joint H s = _ at he
  rw [he]
  congr 2
  funext p
  unfold proposalLog
  congr 2
  have he₁ : p.2-(p.1-s^2 • gradient H p.1) = p.2-p.1+s^2 • gradient H p.1 := by abel
  rw [he₁,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

lemma measurable_joint_map (hH : ContDiff ℝ 2 H) (s : ℝ) :
    Measurable (fun p : Point d × Point d => (p.1,proposal H s p.1 p.2)) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous.measurable
  unfold proposal
  fun_prop

lemma jointCoefficient_ne_zero (hp : partition H ≠ ⊤) {s : ℝ} (hs : s ≠ 0) :
    jointCoefficient H s ≠ 0 := by
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hp)
    (ne_of_gt (EulerDensity.noiseCoefficient_positive d
      (mul_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)) hs)))

lemma jointCoefficient_ne_top (hp : partition H ≠ 0) (s : ℝ) :
    jointCoefficient H s ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp) (EulerDensity.noiseCoefficient_finite d _)

lemma scaled_log_ratio_integrable (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) (μ : Measure (Point d)) [IsFiniteMeasure μ]
    (hi : Integrable (fun x => ‖gradient H x‖^2) μ) {s : ℝ} (hs : |s| ≤ 1) :
    Integrable (fun p : Point d × Point d =>
      |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
        proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|)
      (μ.prod (stdGaussian (Point d))) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hz : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (Point d))).norm.integrable_sq
  refine (((hi.comp_fst (stdGaussian (Point d))).add (hz.comp_snd μ)).const_mul
    (6*(M:ℝ)+(M:ℝ)^2)).mono' ?_ ?_
  · have hc : Continuous (fun p : Point d × Point d =>
        |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
          proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|) := by
      unfold proposalLog proposal
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_eq_abs,abs_abs]
    exact (scaled_log_ratio_bound hH hM hs p.1 p.2).trans (quadratic_dominator_bound M p.1 p.2)

end EulerDefect
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerDefect
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {d : ℕ} {H : Point d → ℝ}

def rate (H : Point d → ℝ) (s : ℝ) : ℝ :=
  ∫ p : Point d × Point d,
    |(proposalLog H (s^2) p.1 (proposal H s p.1 p.2)-
      proposalLog H (s^2) (proposal H s p.1 p.2) p.1)/s^2|
    ∂(gibbs H).prod (stdGaussian (Point d))

lemma rate_nonneg (H : Point d → ℝ) (s : ℝ) : 0 ≤ rate H s :=
  integral_nonneg (fun _ => abs_nonneg _)

lemma rate_tendsto (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) [IsFiniteMeasure (gibbs H)]
    (hi : Integrable (fun x => ‖gradient H x‖^2) (gibbs H)) :
    Filter.Tendsto (rate H) (𝓝 0) (𝓝 0) :=
  expected_scaled_log_ratio_tendsto hH hM (gibbs H) hi

lemma joint_log_ratio_integrable (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) [IsFiniteMeasure (gibbs H)]
    (hi : Integrable (fun x => ‖gradient H x‖^2) (gibbs H))
    {s : ℝ} (hs : s ≠ 0) (hs1 : |s| ≤ 1) :
    Integrable (fun p : Point d × Point d => |proposalLog H (s^2) p.1 p.2-proposalLog H (s^2) p.2 p.1|)
      (joint H s) := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hc : Continuous (fun p : Point d × Point d =>
      |proposalLog H (s^2) p.1 p.2-proposalLog H (s^2) p.2 p.1|) := by
    unfold proposalLog
    fun_prop
  rw [joint,integrable_map_measure hc.aestronglyMeasurable (measurable_joint_map hH s).aemeasurable]
  have hb := (scaled_log_ratio_integrable hH hM (gibbs H) hi hs1).const_mul (s^2)
  convert! hb using 1
  funext p
  dsimp only [Function.comp_apply]
  rw [abs_div,abs_of_nonneg (sq_nonneg s)]
  field_simp

lemma joint_log_ratio_integral (hH : ContDiff ℝ 2 H) {s : ℝ} (hs : s ≠ 0) :
    (∫ p : Point d × Point d, |proposalLog H (s^2) p.1 p.2-proposalLog H (s^2) p.2 p.1|
      ∂joint H s) = s^2*rate H s := by
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hc : Continuous (fun p : Point d × Point d =>
      |proposalLog H (s^2) p.1 p.2-proposalLog H (s^2) p.2 p.1|) := by
    unfold proposalLog
    fun_prop
  rw [joint,integral_map (measurable_joint_map hH s).aemeasurable hc.aestronglyMeasurable,
    rate,← integral_const_mul]
  congr 1
  funext p
  rw [abs_div,abs_of_nonneg (sq_nonneg s)]
  field_simp

theorem one_step_gibbs_defect (hH : ContDiff ℝ 2 H) {M : ℝ≥0}
    (hM : LipschitzWith M (gradient H)) [IsProbabilityMeasure (gibbs H)]
    (hp0 : partition H ≠ 0) (hpt : partition H ≠ ⊤)
    (hi : Integrable (fun x => ‖gradient H x‖^2) (gibbs H))
    {s : ℝ} (hs : s ≠ 0) (hs1 : |s| ≤ 1)
    {f : Point d → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    |(∫ p : Point d × Point d, f (proposal H s p.1 p.2)
        ∂(gibbs H).prod (stdGaussian (Point d)))-∫ x, f x ∂gibbs H| ≤
      B*(2*s^2*rate H s) := by
  have : IsProbabilityMeasure (joint H s) := by
    unfold joint
    infer_instance
  have he := joint_density hH hs
  have : IsProbabilityMeasure (MetropolisBalance.densityLaw volume (jointCoefficient H s)
      (fun p => proposalLog H (s^2) p.1 p.2)) := by rw [← he]; infer_instance
  have hg := (Trapezoid.contDiff_gradient hH).continuous
  have hm : Measurable (fun p : Point d × Point d => proposalLog H (s^2) p.1 p.2) := by
    have hc := hH.continuous
    unfold proposalLog
    fun_prop
  have hr := joint_log_ratio_integrable hH hM hi hs hs1
  rw [he] at hr
  have hh := MetropolisBalance.probability_one_step_defect volume hm
    (jointCoefficient_ne_zero hpt hs) (jointCoefficient_ne_top hp0 s) hr hf hB hb
  rw [← he] at hh
  simp only [Prod.swap] at hh
  rw [joint_log_ratio_integral hH hs] at hh
  have hfst : (∫ p : Point d × Point d, f p.1 ∂joint H s) = ∫ x, f x ∂gibbs H := by
    rw [joint,integral_map (f := fun p : Point d × Point d => f p.1) (measurable_joint_map hH s).aemeasurable
      (hf.comp measurable_fst).aestronglyMeasurable]
    simp only [integral_fun_fst,probReal_univ,one_smul]
  have hsnd : (∫ p : Point d × Point d, f p.2 ∂joint H s) =
      ∫ p : Point d × Point d, f (proposal H s p.1 p.2)
        ∂(gibbs H).prod (stdGaussian (Point d)) := by
    exact integral_map (measurable_joint_map hH s).aemeasurable
      (hf.comp measurable_snd).aestronglyMeasurable
  rw [hfst,hsnd] at hh
  nlinarith only [hh]

end EulerDefect
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
