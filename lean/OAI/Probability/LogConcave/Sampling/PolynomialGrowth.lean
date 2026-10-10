import Mathlib
import OAI.Probability.LogConcave.Analysis.PrimitivePotentialModeBounds

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma integrable_even_norm_pow_gaussian (d n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Point d => ‖x‖^(2*n) * Real.exp (-b*‖x‖^2)) := by
  induction n generalizing b with
  | zero => simpa using integrable_gaussian_envelope d hb
  | succ n ih =>
      have hc : Continuous (fun x : Point d => ‖x‖^(2*(n+1)) * Real.exp (-b*‖x‖^2)) := by fun_prop
      apply ((ih (b := b/2) (by positivity)).const_mul (2/b)).mono' hc.aestronglyMeasurable
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh := mul_le_mul_of_nonneg_left (polynomial_gaussian_absorb hb (sq_nonneg ‖x‖))
        (show 0 ≤ ‖x‖^(2*n) by positivity)
      convert! hh using 1 <;> simp only [Nat.mul_add,pow_add,pow_two] <;> ring

lemma integrable_norm_pow_gaussian (d n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Point d => ‖x‖^n * Real.exp (-b*‖x‖^2)) := by
  have hc : Continuous (fun x : Point d => ‖x‖^n * Real.exp (-b*‖x‖^2)) := by fun_prop
  apply ((integrable_gaussian_envelope d hb).add
    (integrable_even_norm_pow_gaussian d n hb)).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh : ‖x‖^n ≤ 1+‖x‖^(2*n) := by
    rw [mul_comm 2 n,pow_mul]
    nlinarith [sq_nonneg (‖x‖^n-1)]
  simpa only [Pi.add_apply,one_mul,add_mul] using mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

def HasPolynomialGrowth {d : ℕ} {E : Type*} [NormedAddCommGroup E] (h : Point d → E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ z, ‖h z‖ ≤ C*(1+‖z‖^n)

def HasGaussianLowerTail {d : ℕ} (H : Point d → ℝ) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∃ C : ℝ, ∀ z, m*‖z‖^2 ≤ H z + C

def tiltedIntegral {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Point d → ℝ) (h : Point d → E) (θ : Point d) : E :=
  ∫ z, Real.exp (inner ℝ θ z-H z) • h z

lemma gaussian_tilt_bound {d : ℕ} {H : Point d → ℝ} {m C M : ℝ}
    (hm : 0 < m) (_hM : 0 ≤ M) (ht : ∀ z, m*‖z‖^2 ≤ H z+C)
    {θ : Point d} (hθ : ‖θ‖ ≤ M) (z : Point d) :
    Real.exp (inner ℝ θ z-H z) ≤
      Real.exp (C+M^2/(2*m)) * Real.exp (-(m/2)*‖z‖^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hip := (real_inner_le_norm θ z).trans (mul_le_mul_of_nonneg_right hθ (norm_nonneg z))
  have hy : M*‖z‖ ≤ (m/2)*‖z‖^2+M^2/(2*m) := by
    have hh := sq_nonneg (m*‖z‖-M)
    have hd : M^2/(2*m)*(2*m) = M^2 := by field_simp
    nlinarith
  linarith [ht z]

section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integrable_tilted (H : Point d → ℝ) {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) (ht : HasGaussianLowerTail H)
    (hg : HasPolynomialGrowth h) (θ : Point d) :
    Integrable (fun z => Real.exp (inner ℝ θ z-H z) • h z) := by
  obtain ⟨m,hm,C,ht⟩ := ht
  obtain ⟨K,hK,n,hg⟩ := hg
  let B := Real.exp (C+‖θ‖^2/(2*m)) * K
  apply (((integrable_gaussian_envelope d (b := m/2) (by positivity)).add
    (integrable_norm_pow_gaussian d n (b := m/2) (by positivity))).const_mul B).mono'
      ((Real.continuous_exp.comp ((continuous_const.inner continuous_id).sub hH)).smul hh).aestronglyMeasurable
  filter_upwards [] with z
  change ‖Real.exp (inner ℝ θ z-H z) • h z‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he := mul_le_mul (gaussian_tilt_bound hm (norm_nonneg θ) ht le_rfl z)
    (hg z) (norm_nonneg _) (by positivity)
  convert! he using 1; dsimp [B]; ring

def tiltDerivativeIntegrand (h : Point d → E) (z : Point d) : Point d →L[ℝ] E :=
  (innerSL ℝ z).smulRight (h z)

lemma continuous_tiltDerivativeIntegrand {h : Point d → E} (hh : Continuous h) :
    Continuous (tiltDerivativeIntegrand h) := by
  exact isBoundedBilinearMap_smulRight.continuous.comp
    ((innerSL ℝ).continuous.prodMk hh)

lemma growth_tiltDerivativeIntegrand {h : Point d → E} (hg : HasPolynomialGrowth h) :
    HasPolynomialGrowth (tiltDerivativeIntegrand h) := by
  obtain ⟨C,hC,n,hn⟩ := hg
  refine ⟨2*C,by positivity,n+1,fun z => ?_⟩
  have hb : ‖tiltDerivativeIntegrand h z‖ ≤ ‖z‖ * ‖h z‖ := by
    simp [tiltDerivativeIntegrand, ContinuousLinearMap.norm_smulRight_apply]
  have hr : ‖z‖ ≤ 1+‖z‖^(n+1) := by
    by_cases hz : ‖z‖ ≤ 1
    · have hh : 0 ≤ ‖z‖^(n+1) := by positivity
      linarith
    · have hz' : 1 ≤ ‖z‖ := le_of_not_ge hz
      have hn' : 1 ≤ ‖z‖^n := one_le_pow₀ hz'
      have hh := mul_le_mul_of_nonneg_left hn' (norm_nonneg z)
      rw [← pow_succ',mul_one] at hh
      linarith
  calc
    _ ≤ ‖z‖ * (C*(1+‖z‖^n)) := hb.trans (mul_le_mul_of_nonneg_left (hn z) (norm_nonneg z))
    _ ≤ 2*C*(1+‖z‖^(n+1)) := by
      have hr' := mul_le_mul_of_nonneg_left hr hC
      have hp : ‖z‖*‖z‖^n = ‖z‖^(n+1) := (pow_succ' _ _).symm
      have hnon : 0 ≤ C*‖z‖^(n+1) := by positivity
      nlinarith [mul_nonneg hC (show 0 ≤ 1+‖z‖^(n+1) by positivity)]

theorem hasFDerivAt_tiltedIntegral (H : Point d → ℝ) {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) (ht : HasGaussianLowerTail H)
    (hg : HasPolynomialGrowth h) (θ : Point d) :
    HasFDerivAt (tiltedIntegral H h) (tiltedIntegral H (tiltDerivativeIntegrand h) θ) θ := by
  obtain ⟨m,hm,C,hT⟩ := ht
  have ht : HasGaussianLowerTail H := ⟨m,hm,C,hT⟩
  obtain ⟨K,hK,n,hg'⟩ := growth_tiltDerivativeIntegrand hg
  let M := ‖θ‖+1
  let B := Real.exp (C+M^2/(2*m))*K
  let b : Point d → ℝ := fun z => B*(Real.exp (-(m/2)*‖z‖^2)+
    ‖z‖^n*Real.exp (-(m/2)*‖z‖^2))
  have hi : Integrable b := ((integrable_gaussian_envelope d (b := m/2) (by positivity)).add
    (integrable_norm_pow_gaussian d n (b := m/2) (by positivity))).const_mul B
  have hd : ∀ z θ', HasFDerivAt
      (fun t : Point d => Real.exp (inner ℝ t z-H z) • h z)
      (Real.exp (inner ℝ θ' z-H z) • tiltDerivativeIntegrand h z) θ' := by
    intro z θ'
    have hh' := (((innerSL ℝ z).hasFDerivAt (x := θ')).sub_const (H z)).exp.smul_const (h z)
    convert! hh' using 1
    · funext t
      simp only [innerSL_apply_apply, real_inner_comm t z]
    · ext t
      simp [tiltDerivativeIntegrand,real_inner_comm,smul_smul]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun t z => Real.exp (inner ℝ t z-H z) • tiltDerivativeIntegrand h z)
    (bound := b) (Metric.ball_mem_nhds θ (show (0:ℝ)<1 by norm_num))
  · exact Filter.Eventually.of_forall fun t => (integrable_tilted H hH hh ht hg t).aestronglyMeasurable
  · exact integrable_tilted H hH hh ht hg θ
  · exact (integrable_tilted H hH (continuous_tiltDerivativeIntegrand hh) ht
      (growth_tiltDerivativeIntegrand hg) θ).aestronglyMeasurable
  · filter_upwards [] with z t ht'
    have htm : ‖t‖ ≤ M := by
      have hb : ‖t-θ‖ < 1 := by simpa [dist_eq_norm] using ht'
      have hn := norm_add_le (t-θ) θ
      simp only [sub_add_cancel] at hn
      dsimp [M]
      linarith
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have he := mul_le_mul (gaussian_tilt_bound hm (by dsimp [M]; positivity) hT htm z)
      (hg' z) (norm_nonneg _) (by positivity)
    change _ ≤ B*(Real.exp (-(m/2)*‖z‖^2)+‖z‖^n*Real.exp (-(m/2)*‖z‖^2))
    convert! he using 1; dsimp [B]; ring
  · exact hi
  · exact Filter.Eventually.of_forall fun z θ' _ => hd z θ'

theorem contDiff_tiltedIntegral (H : Point d → ℝ) {h : Point d → E}
    (hH : Continuous H) (hh : Continuous h) (ht : HasGaussianLowerTail H)
    (hg : HasPolynomialGrowth h) : ContDiff ℝ (⊤ : ℕ∞) (tiltedIntegral H h) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing E with
  | zero =>
      exact contDiff_zero.mpr (show Differentiable ℝ (tiltedIntegral H h) from
        fun θ => (hasFDerivAt_tiltedIntegral H hH hh ht hg θ).differentiableAt).continuous
  | succ n ih =>
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_fderiv]
      refine ⟨fun θ => (hasFDerivAt_tiltedIntegral H hH hh ht hg θ).differentiableAt, ?_, ?_⟩
      · simp
      · have hf : fderiv ℝ (tiltedIntegral H h) = tiltedIntegral H (tiltDerivativeIntegrand h) := by
          funext θ
          exact (hasFDerivAt_tiltedIntegral H hH hh ht hg θ).fderiv
        rw [hf]
        exact ih (continuous_tiltDerivativeIntegrand hh) (growth_tiltDerivativeIntegrand hg)

end
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
