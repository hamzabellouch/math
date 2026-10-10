import Mathlib
import OAI.Probability.SphericalField.Gaussian.Quadratic

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
lemma standardGaussian_quadratic_integral {a : ℝ} (ha : a < 1/2) (c d : ℝ) :
    (∫ y, Real.exp (a*y^2+c*y+d) ∂gaussianReal 0 1) =
      Real.exp (d+c^2/(4*(1/2-a))) / Real.sqrt (1-2*a) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul,standardGaussian_quadratic_density]
  rw [integral_const_mul,real_quadratic_integral (by linarith : 0 < 1/2-a)]
  have hratio : Real.sqrt (Real.pi/(1/2-a)) = Real.sqrt (2*Real.pi)/Real.sqrt (1-2*a) := by
    rw [←Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  rw [hratio]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 2*Real.pi))]

lemma gaussian_quadratic_fractional_integrable {b z σ : ℝ} (hb : 0 < b)
    (ha : 0 < b-z*σ^2) (c x : ℝ) :
    Integrable (fun y : ℝ => Real.exp (z*(c+(x+σ*y)^2/(2*b)))) (gaussianReal 0 1) := by
  have hhalf : z*σ^2/(2*b) < 1/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*b)).mpr
    linarith
  convert standardGaussian_quadratic_integrable hhalf (z*x*σ/b) (z*c+z*x^2/(2*b)) using 1
  funext y
  congr 1
  field_simp
  ring

lemma gaussian_quadratic_fractional_log {b z σ : ℝ} (hb : 0 < b) (hz : z ≠ 0)
    (ha : 0 < b-z*σ^2) (c x : ℝ) :
    Real.log (∫ y, Real.exp (z*(c+(x+σ*y)^2/(2*b))) ∂gaussianReal 0 1)/z =
      c+(Real.log b-Real.log (b-z*σ^2))/(2*z)+x^2/(2*(b-z*σ^2)) := by
  have hhalf : z*σ^2/(2*b) < 1/2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*b)).mpr
    linarith
  have hfun : (fun y : ℝ => Real.exp (z*(c+(x+σ*y)^2/(2*b)))) =
      (fun y : ℝ => Real.exp ((z*σ^2/(2*b))*y^2+(z*x*σ/b)*y+(z*c+z*x^2/(2*b)))) := by
    funext y
    congr 1
    field_simp
    ring
  have hprec : 1-2*(z*σ^2/(2*b)) = (b-z*σ^2)/b := by field_simp
  have hprec' : 1/2-z*σ^2/(2*b) = (b-z*σ^2)/(2*b) := by field_simp
  rw [hfun,standardGaussian_quadratic_integral hhalf,hprec,
    Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr (div_pos ha hb)).ne',
    Real.log_exp, Real.log_sqrt (div_pos ha hb).le,Real.log_div ha.ne' hb.ne',hprec']
  field_simp [hb.ne',hz,ha.ne']
  ring

lemma gaussianShiftStep_measurable (σ : ℕ → ℝ) : Measurable (gaussianShiftStep σ) := by
  unfold gaussianShiftStep
  fun_prop

def quadraticCascadePrecision (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => b
  | n+1, z => quadraticCascadePrecision σ b n (fun i => z i.succ)-z 0*(σ n)^2

def quadraticCascadeOffset (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, z => quadraticCascadeOffset σ b n (fun i => z i.succ)+
      (Real.log (quadraticCascadePrecision σ b n (fun i => z i.succ))-
        Real.log (quadraticCascadePrecision σ b (n+1) z))/(2*z 0)

lemma quadraticCascadePrecision_tail_pos (σ : ℕ → ℝ) (b : ℝ) (n : ℕ) (z : Fin (n+1) → ℝ)
    (hz : 0 ≤ z 0) (hp : 0 < quadraticCascadePrecision σ b (n+1) z) :
    0 < quadraticCascadePrecision σ b n (fun i => z i.succ) := by
  have hsq := mul_nonneg hz (sq_nonneg (σ n))
  dsimp [quadraticCascadePrecision] at hp
  linarith

theorem finiteCascade_quadratic_recursion (σ : ℕ → ℝ) (b c : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hp : 0 < quadraticCascadePrecision σ b n z) :
    (∀ x : ℕ → ℝ, finiteCascadeLogRecursion standardGaussianMark (gaussianShiftStep σ) n z
      (fun x => c+(x 0)^2/(2*b)) x =
      c+quadraticCascadeOffset σ b n z+(x n)^2/(2*quadraticCascadePrecision σ b n z)) ∧
    finiteCascadeFractionalIntegrable standardGaussianMark (gaussianShiftStep σ)
      (fun x => c+(x 0)^2/(2*b)) n z := by
  induction n with
  | zero => exact ⟨fun _ => by simp [finiteCascadeLogRecursion,quadraticCascadeOffset,quadraticCascadePrecision],trivial⟩
  | succ n ih =>
    have hpt := quadraticCascadePrecision_tail_pos σ b n z (hz 0).le hp
    obtain ⟨heq,hint⟩ := ih (fun i => z i.succ) (fun i => hz i.succ) hpt
    constructor
    · intro x
      conv_lhs => rw [finiteCascadeLogRecursion]
      unfold fractionalLogMoment
      simp_rw [heq]
      change Real.log (∫ y, Real.exp (z 0 *
        (c+quadraticCascadeOffset σ b n (fun i => z i.succ)+
          (x (n+1)+σ n*y)^2/(2*quadraticCascadePrecision σ b n (fun i => z i.succ))))
          ∂gaussianReal 0 1)/(z 0) = _
      rw [gaussian_quadratic_fractional_log hpt (hz 0).ne' hp]
      dsimp [quadraticCascadeOffset,quadraticCascadePrecision]
      ring
    · refine ⟨?_,hint⟩
      intro x
      simp_rw [heq]
      exact gaussian_quadratic_fractional_integrable hpt hp
        (c+quadraticCascadeOffset σ b n (fun i => z i.succ)) (x (n+1))

theorem canonical_cascade_quadratic_log (σ : ℕ → ℝ) (b c : ℝ)
    (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b n z) (x : ℕ → ℝ) :
    (∫ η, Real.log (decoratedTerminalTotal (gaussianShiftStep σ) (fun x => c+(x 0)^2/(2*b)) n (x,η) /
      decoratedTerminalTotal (gaussianShiftStep σ) (fun _ => 0) n (x,η))
        ∂decoratedCascadeLaw standardGaussianMark n z) =
      c+quadraticCascadeOffset σ b n z+(x n)^2/(2*quadraticCascadePrecision σ b n z) := by
  have hq := finiteCascade_quadratic_recursion σ b c n z hz0 hp
  rw [finiteCascade_terminal_log_recursion_of_fractional standardGaussianMark (gaussianShiftStep σ)
    (gaussianShiftStep_measurable σ) n z hz hz0 hz1 (by fun_prop) hq.2]
  exact hq.1 x

lemma canonical_scalar_integrable {b : ℝ} (hb : 0 < b) (u : ℝ) :
    Integrable (fun y : ℝ => Real.exp ((1-b)*y^2/2+u*y)) (gaussianReal 0 1) := by
  convert standardGaussian_quadratic_integrable (a := (1-b)/2) (by linarith) u 0 using 1
  funext y
  congr 1
  ring

lemma canonical_scalar_integral {b : ℝ} (hb : 0 < b) (u : ℝ) :
    (∫ y, Real.exp ((1-b)*y^2/2+u*y) ∂gaussianReal 0 1) =
      Real.exp (u^2/(2*b))/Real.sqrt b := by
  have he : (fun y : ℝ => Real.exp ((1-b)*y^2/2+u*y)) =
      (fun y : ℝ => Real.exp (((1-b)/2)*y^2+u*y+0)) := by funext y; congr 1; ring
  rw [he,standardGaussian_quadratic_integral (by linarith : (1-b)/2 < 1/2)]
  congr 2 <;> ring

lemma canonical_scalar_log {b : ℝ} (hb : 0 < b) (u : ℝ) :
    Real.log (∫ y, Real.exp ((1-b)*y^2/2+u*y) ∂gaussianReal 0 1) =
      -Real.log b/2+u^2/(2*b) := by
  rw [canonical_scalar_integral hb,Real.log_div (Real.exp_pos _).ne' (Real.sqrt_pos.mpr hb).ne',
    Real.log_exp,Real.log_sqrt hb.le]
  ring

lemma quadraticCascadePrecision_le (σ : ℕ → ℝ) (b : ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) : quadraticCascadePrecision σ b n z ≤ b := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have ht := ih (fun i => z i.succ) (fun i => hz i.succ)
    have hq := mul_nonneg (hz 0) (sq_nonneg (σ n))
    dsimp [quadraticCascadePrecision]
    linarith

lemma quadraticCascadePrecision_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ) (b : ℝ) :
    HasDerivAt (fun b => quadraticCascadePrecision σ b n z) 1 b := by
  induction n with
  | zero => exact hasDerivAt_id b
  | succ n ih => exact (ih (fun i => z i.succ)).sub_const _

def quadraticCascadeReciprocalSlope (σ : ℕ → ℝ) (b : ℝ) : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, z => quadraticCascadeReciprocalSlope σ b n (fun i => z i.succ)+
      (1/(quadraticCascadePrecision σ b n (fun i => z i.succ))-
        1/(quadraticCascadePrecision σ b (n+1) z))/(2*z 0)

lemma quadraticCascadeOffset_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) {b : ℝ} (hp : 0 < quadraticCascadePrecision σ b n z) :
    HasDerivAt (fun b => quadraticCascadeOffset σ b n z)
      (quadraticCascadeReciprocalSlope σ b n z) b := by
  induction n with
  | zero => exact hasDerivAt_const b 0
  | succ n ih =>
    have hpt := quadraticCascadePrecision_tail_pos σ b n z (hz 0) hp
    exact (ih (fun i => z i.succ) (fun i => hz i.succ) hpt).add
      ((((quadraticCascadePrecision_hasDerivAt σ n (fun i => z i.succ) b).log hpt.ne').sub
        ((quadraticCascadePrecision_hasDerivAt σ (n+1) z b).log hp.ne')).div_const (2*z 0))

def canonicalGaussianFreeValue (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ) (r b : ℝ) : ℝ :=
  -Real.log b/2 + quadraticCascadeOffset σ b n z+r/(2*quadraticCascadePrecision σ b n z)

lemma canonicalGaussianFreeValue_hasDerivAt (σ : ℕ → ℝ) (n : ℕ) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) (r : ℝ) {b : ℝ} (hp : 0 < quadraticCascadePrecision σ b n z) :
    HasDerivAt (canonicalGaussianFreeValue σ n z r)
      (-1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-r/(2*(quadraticCascadePrecision σ b n z)^2)) b := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b n z hz)
  have hq := quadraticCascadePrecision_hasDerivAt σ n z b
  have ht := (((Real.hasDerivAt_log hb.ne').neg.div_const 2).add
    (quadraticCascadeOffset_hasDerivAt σ n z hz hp)).add
      ((hasDerivAt_const b r).div (hq.const_mul 2) (by positivity))
  have hd : -b⁻¹/2+quadraticCascadeReciprocalSlope σ b n z+
      (0*(2*quadraticCascadePrecision σ b n z)-r*(2*1))/(2*quadraticCascadePrecision σ b n z)^2 =
      -1/(2*b)+quadraticCascadeReciprocalSlope σ b n z-r/(2*(quadraticCascadePrecision σ b n z)^2) := by
    field_simp [hb.ne',hp.ne']
    ring
  exact ht.congr_deriv hd

end SphericalPerceptron
end
end
end

end OAI
