import Mathlib

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
namespace PrimeDegreePackets.AnalyticGrowth

 

lemma exists_disk_logarithm {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hzero : ∀ z ∈ ball 0 R, g z ≠ 0) :
    ∃ h : ℂ → ℂ, h 0 = 0 ∧
      (∀ z ∈ ball 0 R, HasDerivAt h (logDeriv g z) z) ∧
      (∀ z ∈ ball 0 R, Complex.exp (h z) = g z / g 0) := by
  have hga : AnalyticOnNhd ℂ g (ball 0 R) := hg.analyticOnNhd isOpen_ball
  have hld : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    exact (((hga z hz).deriv.differentiableAt).div
      ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)) (hzero z hz)).differentiableWithinAt
  obtain ⟨h,h0,hh⟩ := hld.isExactOn_ball.with_val_at 0 0
  refine ⟨h,h0,hh,?_⟩
  have HD : ∀ z ∈ ball 0 R,
      HasDerivAt (fun z => g z * Complex.exp (-h z)) 0 z := by
    intro z hz
    have H := ((hg z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.mul ((hh z hz).neg.cexp)
    apply H.congr_deriv
    dsimp only [Pi.neg_apply, logDeriv_apply]
    field_simp [hzero z hz]
    ring
  have HE : EqOn (fun z => g z * Complex.exp (-h z)) (fun _ => g 0) (ball 0 R) := by
    apply isOpen_ball.eqOn_of_deriv_eq (convex_ball (0:ℂ) R).isPreconnected
      (fun z hz => (HD z hz).differentiableAt.differentiableWithinAt)
      (differentiableOn_const _) (fun z hz => by rw [(HD z hz).deriv, deriv_const])
      (mem_ball_self hR)
    simp [h0]
  intro z hz
  have H := HE hz
  rw [eq_div_iff (hzero 0 (mem_ball_self hR))]
  have He : Complex.exp (-h z) * Complex.exp (h z) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have HH := congrArg (fun w => w*Complex.exp (h z)) H
  rw [mul_assoc, He, mul_one] at HH
  exact (mul_comm _ _).trans HH.symm

lemma disk_logarithm_re {g h : ℂ → ℂ} {z : ℂ}
    (hzero : g 0 ≠ 0) (hz : Complex.exp (h z) = g z / g 0) :
    (h z).re = Real.log ‖g z‖ - Real.log ‖g 0‖ := by
  have Hg : g z ≠ 0 := by
    intro H
    rw [H, zero_div] at hz
    exact Complex.exp_ne_zero _ hz
  have H := congrArg (fun w : ℂ => Real.log ‖w‖) hz
  simpa only [Complex.norm_exp, Real.log_exp, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr Hg) (norm_ne_zero_iff.mpr hzero)] using H

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma deriv_sub_le_of_re_le {h : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hh : DifferentiableOn ℂ h (ball 0 R)) (h0 : h 0 = 0)
    (hreal : ∀ z ∈ ball 0 R, (h z).re ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.ball 0 (R/4)) (hw : w ∈ Metric.ball 0 (R/4)) :
    ‖deriv h z - deriv h w‖ ≤ (64*M/R^2)*‖z-w‖ := by
  have HR4 : 0 < R/4 := by positivity
  have HE : ∀ a ∈ Metric.ball (0:ℂ) (R/4),
      closedBall a (R/4) ⊆ ball (0:ℂ) R := by
    intro a ha b hb
    rw [mem_ball_zero_iff] at ha ⊢
    have HB := norm_le_norm_sub_add b a
    have HH : ‖b-a‖ ≤ R/4 := by simpa [dist_eq_norm] using hb
    linarith
  have HB : ∀ a ∈ Metric.ball (0:ℂ) (R/4), ∀ b ∈ sphere a (R/4), ‖h b‖ ≤ 2*M := by
    intro a ha b hb
    have Hba : ‖b-a‖ = R/4 := by simpa [dist_eq_norm] using hb
    have Ha : ‖a‖ < R/4 := mem_ball_zero_iff.mp ha
    have Hb : ‖b‖ < R/2 := by linarith [norm_le_norm_sub_add b a]
    have HBR : b ∈ ball (0:ℂ) R := mem_ball_zero_iff.mpr (by linarith)
    have H := Complex.borelCaratheodory_zero hM hh (fun x hx => hreal x hx) hR HBR h0
    apply H.trans
    rw [div_le_iff₀ (by linarith : 0 < R-‖b‖)]
    nlinarith
  have H2 : ∀ a ∈ Metric.ball (0:ℂ) (R/4),
      ‖deriv (deriv h) a‖ ≤ 64*M/R^2 := by
    intro a ha
    have H := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      2 HR4 (hh.diffContOnCl_ball (HE a ha)) (HB a ha)
    have HN : (2:ℝ)*(2*M)/(R/4)^2 = 64*M/R^2 := by ring
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial_two,
      Nat.cast_ofNat, HN] using H
  apply Convex.norm_image_sub_le_of_norm_deriv_le _ H2 (convex_ball (0:ℂ) (R/4)) hw hz
  intro a ha
  apply ((hh.analyticOnNhd isOpen_ball) a (HE a ha (mem_closedBall_self HR4.le))).deriv.differentiableAt

 

lemma logDeriv_sub_le_of_log_norm_le {g : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball 0 R))
    (hzero : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hbound : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M)
    {z w : ℂ} (hz : z ∈ Metric.ball 0 (R/4)) (hw : w ∈ Metric.ball 0 (R/4)) :
    ‖logDeriv g z - logDeriv g w‖ ≤ (64*M/R^2)*‖z-w‖ := by
  obtain ⟨h,h0,hh,HE⟩ := exists_disk_logarithm hR hg hzero
  have hh' : DifferentiableOn ℂ h (ball 0 R) :=
    fun z hz => (hh z hz).differentiableAt.differentiableWithinAt
  have H := deriv_sub_le_of_re_le hR hM hh' h0 (fun z hz => by
    rw [disk_logarithm_re (hzero 0 (mem_ball_self hR)) (HE z hz)]
    exact hbound z hz) hz hw
  have hs : Metric.ball (0:ℂ) (R/4) ⊆ ball 0 R := ball_subset_ball (by linarith)
  rwa [(hh z (hs hz)).deriv, (hh w (hs hw)).deriv] at H

end PrimeDegreePackets.AnalyticGrowth

open Complex Set Metric Filter MeromorphicOn
namespace PrimeDegreePackets.AnalyticGrowth

lemma entire_order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (z : ℂ) : meromorphicOrderAt f z ≠ ⊤ := by
  have HM : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  apply HM.exists_meromorphicOrderAt_ne_top_iff_forall.mp
  use 0
  rw [(hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
  simp

lemma divisor_sphere_eq_zero {f : ℂ → ℂ} {R : ℝ} (hf : Differentiable ℂ f)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) : divisor f (sphere 0 R) = 0 := by
  ext z
  by_cases hz : z ∈ sphere (0:ℂ) R
  · rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) hz,
      (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hz)]
    simp
  · simp only [divisor_def, hz, and_false, ite_false, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]

lemma exists_entire_ecanonicalDecomp {f : ℂ → ℂ} {R : ℝ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    ∃ g, ECanonicalDecomp f g R := by
  exact MeromorphicOn.exists_ecanonicalDecomp (fun z _ => (hf.analyticAt z).meromorphicAt)
    (fun z => entire_order_ne_top hf h0 z)

lemma ecanonical_log_norm_eq_on_sphere {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ} (hz : z ∈ sphere (0:ℂ) R) :
    Real.log ‖g z‖ = Real.log ‖f z‖ := by
  rw [D.log_norm_eq (sphere_subset_closedBall hz)
    ((hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (hS z hz)) hR,
    (hf.analyticAt z).meromorphicTrailingCoeffAt_of_ne_zero (hS z hz),
    divisor_sphere_eq_zero hf hS]
  suffices (∑ᶠ i, (divisor f (ball (0:ℂ) R) i : ℝ) *
      Real.log ‖canonicalFactor R i z‖) = 0 by simp [this]
  trans ∑ᶠ _i : ℂ, (0:ℝ)
  · apply finsum_congr
    intro i
    by_cases hi : divisor f (ball (0:ℂ) R) i = 0
    · simp [hi]
    · have hiB := (divisor f (ball (0:ℂ) R)).supportWithinDomain hi
      rw [norm_canonicalFactor_eval_circle_eq_one hiB hz, Real.log_one, mul_zero]
  · exact finsum_zero

lemma norm_canonicalFactor_zero {R : ℝ} {i : ℂ} (hR : 0 < R) :
    ‖canonicalFactor R i 0‖ = R/‖i‖ := by
  simp only [canonicalFactor_apply, mul_zero, sub_zero, zero_sub, norm_div,
    norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul, norm_neg]
  by_cases hi : i = 0
  · simp [hi]
  · field_simp

lemma ecanonical_log_norm_zero_ge {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) (h0 : f 0 ≠ 0) :
    Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := by
  rw [D.log_norm_eq (mem_closedBall_self hR.le)
    ((hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0) hR,
    (hf.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero h0,
    divisor_sphere_eq_zero hf hS]
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero, zero_mul,
    finsum_zero, sub_zero, le_add_iff_nonneg_left]
  apply finsum_nonneg
  intro i
  by_cases hi : divisor f (ball (0:ℂ) R) i = 0
  · simp [hi]
  have hiB := (divisor f (ball (0:ℂ) R)).supportWithinDomain hi
  have hi0 : i ≠ 0 := by
    intro H
    subst i
    rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
      (mem_ball_self hR), (hf.analyticAt 0).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0] at hi
    simp at hi
  apply mul_nonneg
  · exact_mod_cast AnalyticOnNhd.divisor_nonneg (fun z _ => hf.analyticAt z) i
  · rw [norm_canonicalFactor_zero hR]
    apply Real.log_nonneg
    apply (le_div_iff₀ (norm_pos_iff.mpr hi0)).mpr
    simpa using (mem_ball_zero_iff.mp hiB).le

lemma ecanonical_log_norm_le {f g : ℂ → ℂ} {R B : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0)
    (hbound : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ Real.exp B)
    {z : ℂ} (hz : z ∈ closedBall (0:ℂ) R) : Real.log ‖g z‖ ≤ B := by
  apply (Real.log_le_iff_le_exp (norm_pos_iff.mpr (D.ne_zero z hz))).mpr
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := (0:ℂ)) (r := R))
    (D.analyticOnNhd.differentiableOn.diffContOnCl_ball subset_rfl)
  · intro w hw
    have hwS : w ∈ sphere (0:ℂ) R := by simpa [frontier_ball _ hR.ne'] using hw
    have H := ecanonical_log_norm_eq_on_sphere D hf hR hS hwS
    have HE := congrArg Real.exp H
    rw [Real.exp_log (norm_pos_iff.mpr (D.ne_zero w (sphere_subset_closedBall hwS))),
      Real.exp_log (norm_pos_iff.mpr (hS w hwS))] at HE
    exact HE ▸ hbound w hwS
  · simpa [closure_ball _ hR.ne'] using hz

end PrimeDegreePackets.AnalyticGrowth

open scoped Topology ComplexConjugate
namespace PrimeDegreePackets.AnalyticGrowth

def canonicalCorrection (R : ℝ) (ρ z : ℂ) : ℂ := conj ρ / ((R:ℂ)^2-conj ρ*z)

lemma canonicalNumerator_norm_lower {R : ℝ} {ρ z : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) :
    R^2/2 ≤ ‖(R:ℂ)^2-conj ρ*z‖ := by
  have H := norm_sub_norm_le ((R:ℂ)^2) (conj ρ*z)
  simp only [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR,
    norm_mul, norm_conj] at H
  have H' := mul_le_mul hρ hz (norm_nonneg z) hR.le
  nlinarith

lemma canonicalNumerator_ne_zero {R : ℝ} {ρ z : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) : (R:ℂ)^2-conj ρ*z ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (canonicalNumerator_norm_lower hR hρ hz))

lemma norm_canonicalCorrection_sub_le {R : ℝ} {ρ z w : ℂ} (hR : 0 < R)
    (hρ : ‖ρ‖ ≤ R) (hz : ‖z‖ ≤ R/2) (hw : ‖w‖ ≤ R/2) :
    ‖canonicalCorrection R ρ z-canonicalCorrection R ρ w‖ ≤ 4/R^2*‖z-w‖ := by
  have hZ := canonicalNumerator_ne_zero hR hρ hz
  have hW := canonicalNumerator_ne_zero hR hρ hw
  have HE : canonicalCorrection R ρ z-canonicalCorrection R ρ w =
      (conj ρ)^2*(z-w)/(((R:ℂ)^2-conj ρ*z)*((R:ℂ)^2-conj ρ*w)) := by
    unfold canonicalCorrection
    field_simp
    ring
  rw [HE, norm_div, norm_mul, norm_mul, norm_pow, norm_conj]
  have Hden : R^4/4 ≤ ‖(R:ℂ)^2-conj ρ*z‖*‖(R:ℂ)^2-conj ρ*w‖ := by
    have H := mul_le_mul (canonicalNumerator_norm_lower hR hρ hz)
      (canonicalNumerator_norm_lower hR hρ hw) (by positivity : 0 ≤ R^2/2)
      (norm_nonneg _)
    nlinarith
  have Hn : ‖ρ‖^2*‖z-w‖ ≤ R^2*‖z-w‖ :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hρ 2) (norm_nonneg _)
  calc
    _ ≤ R^2*‖z-w‖/(R^4/4) := div_le_div₀ (by positivity) Hn (by positivity) Hden
    _ = _ := by field_simp

lemma logDeriv_canonicalFactor {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0)
    (hz : z ≠ ρ) (hnum : (R:ℂ)^2-conj ρ*z ≠ 0) :
    logDeriv (canonicalFactor R ρ) z = -canonicalCorrection R ρ z - 1/(z-ρ) := by
  have HR : (R:ℂ) ≠ 0 := by exact_mod_cast hR
  have HZ : z-ρ ≠ 0 := sub_ne_zero.mpr hz
  have Hn : HasDerivAt (fun z : ℂ => (R:ℂ)^2-conj ρ*z) (-conj ρ) z := by
    apply ((hasDerivAt_const z ((R:ℂ)^2)).sub
      ((hasDerivAt_id z).const_mul (conj ρ))).congr_deriv
    simp
  have Hd : HasDerivAt (fun z : ℂ => (R:ℂ)*(z-ρ)) (R:ℂ) z := by
    apply (((hasDerivAt_id z).sub_const ρ).const_mul (R:ℂ)).congr_deriv
    simp
  unfold canonicalFactor
  rw [logDeriv_fun_div (g := fun z : ℂ => (R:ℂ)*(z-ρ)) z hnum (mul_ne_zero HR HZ) Hn.differentiableAt Hd.differentiableAt]
  rw [logDeriv_apply, logDeriv_apply, Hn.deriv, Hd.deriv]
  unfold canonicalCorrection
  field_simp

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 

lemma ecanonical_logDeriv {f g : ℂ → ℂ} {R : ℝ}
    (D : ECanonicalDecomp f g R) (hf : Differentiable ℂ f) (hR : 0 < R)
    (hS : ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0) {z : ℂ}
    (hz : ‖z‖ ≤ R/2) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ᶠ ρ, (divisor f (ball (0:ℂ) R) ρ : ℂ) *
      (1/(z-ρ)+canonicalCorrection R ρ z)) + logDeriv g z := by
  classical
  let t := D.meromorphicOn.divisor_ball_support_finite.toFinset
  have ht (ρ : ℂ) : ρ ∈ t ↔ divisor f (ball (0:ℂ) R) ρ ≠ 0 := by
    simp only [t, Set.Finite.mem_toFinset, Function.mem_support]
  have hρB (ρ : ℂ) (hρ : ρ ∈ t) : ρ ∈ ball (0:ℂ) R :=
    (divisor f (ball (0:ℂ) R)).supportWithinDomain ((ht ρ).mp hρ)
  have hzB : z ∈ closedBall (0:ℂ) R := mem_closedBall_zero_iff.mpr (by linarith)
  have havoid (ρ : ℂ) (hρ : ρ ∈ t) : z ≠ ρ := by
    intro H
    obtain rfl := H
    have HH := (ht z).mp hρ
    rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt) (hρB z hρ),
      (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz] at HH
    simp at HH
  let P : ℂ → ℂ := fun x => ∏ ρ ∈ t, canonicalFactor R ρ x ^ (-divisor f (ball 0 R) ρ)
  have HPa : AnalyticAt ℂ P z := by
    apply Finset.analyticAt_fun_prod
    intro ρ hρ
    apply (analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).fun_zpow
    exact canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ)
  have HPz : P z ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    exact zpow_ne_zero _ (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))
  have HP : (∏ᶠ ρ, (canonicalFactor R ρ)^(-divisor f (ball (0:ℂ) R) ρ)) = P := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := t) _ ?_]
    · ext x
      simp only [P, Finset.prod_apply, Pi.pow_apply]
    · intro ρ hρ
      apply (ht ρ).mpr
      intro H
      simp [H] at hρ
  have HE : f =ᶠ[codiscreteWithin (closedBall (0:ℂ) R)] (fun x => P x*g x) := by
    have H := D.eventuallyEq
    rw [HP, divisor_sphere_eq_zero hf hS] at H
    filter_upwards [H] with x hx
    simpa only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, zpow_zero,
      finprod_one, mul_one, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hx
  have HEz : f =ᶠ[𝓝 z] (fun x => P x*g x) := by
    apply ((hf z).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (HPa.mul (D.analyticOnNhd z hzB)).continuousAt).mp
    apply (hf.analyticAt z).meromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (HPa.mul (D.analyticOnNhd z hzB)).meromorphicAt hzB _ HE
    rw [← closure_ball _ hR.ne']
    exact isOpen_ball.perfect_closure.2
  rw [(logDeriv_congr_nhds HEz).eq_of_nhds,
    logDeriv_fun_mul z HPz (D.ne_zero z hzB) HPa.differentiableAt (D.analyticOnNhd z hzB).differentiableAt]
  congr 1
  change logDeriv (fun x => ∏ ρ ∈ t, canonicalFactor R ρ x ^ (-divisor f (ball 0 R) ρ)) z = _
  rw [logDeriv_fun_prod (f := fun ρ x : ℂ => canonicalFactor R ρ x ^
    (-divisor f (ball 0 R) ρ)) (s := t) (x := z) (fun ρ hρ => zpow_ne_zero _
    (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))) (fun ρ hρ =>
      ((analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).fun_zpow
        (canonicalFactor_ne_zero (hρB ρ hρ) hzB (havoid ρ hρ))).differentiableAt)]
  rw [finsum_eq_sum_of_support_subset (s := t) _ (by
    intro ρ hρ
    apply (ht ρ).mpr
    intro H
    simp [H] at hρ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [logDeriv_fun_zpow (analyticOnNhd_canonicalFactor R ρ z (havoid ρ hρ)).differentiableAt,
    logDeriv_canonicalFactor hR.ne' (havoid ρ hρ)
      (canonicalNumerator_ne_zero hR (mem_ball_zero_iff.mp (hρB ρ hρ)).le hz)]
  push_cast
  ring

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.AnalyticGrowth

 
def zeroMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℤ := (meromorphicOrderAt f z).untop₀

lemma zeroMultiplicity_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    0 ≤ zeroMultiplicity f z := by
  have H := AnalyticOnNhd.divisor_nonneg (fun z (_ : z ∈ (univ : Set ℂ)) => hf.analyticAt z) z
  simpa only [zeroMultiplicity, MeromorphicOn.divisor_apply
    (fun z _ => (hf.analyticAt z).meromorphicAt) (mem_univ z),
    Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply] using H

lemma zeroMultiplicity_eq_zero_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (z : ℂ) : zeroMultiplicity f z = 0 ↔ f z ≠ 0 := by
  rw [zeroMultiplicity, WithTop.untop₀_eq_zero]
  simp only [entire_order_ne_top hf h0 z, or_false,
    (hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff]

lemma zeroMultiplicity_ne_zero_iff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (z : ℂ) : zeroMultiplicity f z ≠ 0 ↔ f z = 0 := by
  simp [zeroMultiplicity_eq_zero_iff hf h0]

lemma exists_zero_free_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ R ∈ Ioo a b, ∀ z ∈ sphere (0:ℂ) R, f z ≠ 0 := by
  have Hfin := ((divisor f (closedBall (0:ℂ) b)).finiteSupport (isCompact_closedBall 0 b)).image
    (fun z : ℂ => ‖z‖)
  obtain ⟨R,hR,H⟩ := (Set.Ioo_infinite hab).exists_notMem_finite Hfin
  refine ⟨R,hR,?_⟩
  intro z hz hz0
  apply H
  have HZ : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hz
  refine ⟨z,?_,HZ⟩
  change divisor f (closedBall (0:ℂ) b) z ≠ 0
  rw [MeromorphicOn.divisor_apply (fun z _ => (hf.analyticAt z).meromorphicAt)
    (show z ∈ closedBall (0:ℂ) b from mem_closedBall_zero_iff.mpr (HZ ▸ hR.2.le))]
  exact (zeroMultiplicity_ne_zero_iff hf h0 z).mpr hz0

 
def diskZeroCount (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  ((∑ᶠ z, divisor f (closedBall (0:ℂ) R) z : ℤ) : ℝ)

lemma diskZeroCount_eq_finsum (f : ℂ → ℂ) (R : ℝ) :
    diskZeroCount f R = ∑ᶠ z, (divisor f (closedBall (0:ℂ) R) z : ℝ) := by
  exact map_finsum (Int.castRingHom ℝ)
    ((divisor f (closedBall (0:ℂ) R)).finiteSupport (isCompact_closedBall 0 R))

lemma diskZeroCount_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R : ℝ) :
    0 ≤ diskZeroCount f R := by
  rw [diskZeroCount_eq_finsum]
  apply finsum_nonneg
  intro z
  exact_mod_cast AnalyticOnNhd.divisor_nonneg (fun z _ => hf.analyticAt z) z

 
lemma diskZeroCount_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 2*R → ‖f z‖ ≤ Real.exp B) :
    diskZeroCount f R ≤ (B-Real.log ‖f 0‖)/Real.log 2 := by
  have H := AnalyticOnNhd.sum_divisor_le (f := f) (c := (0:ℂ)) (r := R) (R := 2*R)
    (by simpa [abs_of_pos hR] using hR)
    (by rw [abs_of_pos hR, abs_of_pos (by positivity : 0 < 2*R)]; linarith)
    (Real.one_le_exp_iff.mpr hB) (fun z _ => hf.analyticAt z) h0
    (fun z hz => hbound z (by
      simpa only [abs_of_pos (by positivity : 0 < 2*R)] using
        le_of_eq (mem_sphere_zero_iff_norm.mp hz)))
  rw [abs_of_pos hR] at H
  have HE : 2*R/R = 2 := by field_simp
  simpa only [diskZeroCount, abs_of_pos hR, Real.log_div (Real.exp_ne_zero B)
    (norm_ne_zero_iff.mpr h0), Real.log_exp, HE] using H

end PrimeDegreePackets.AnalyticGrowth
end
end

end OAI
