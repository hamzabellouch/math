import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples

section WaveDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def waveDeriv (v : E) (f : E → ℂ) (x : E) : ℂ := fderiv ℝ f x v

theorem waveDeriv_mul (v : E) (f g : E → ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    waveDeriv v (fun y => f y * g y) x =
      waveDeriv v f x * g x + f x * waveDeriv v g x := by
  simp only [waveDeriv, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

theorem waveDeriv_add (v : E) (f g : E → ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    waveDeriv v (fun y => f y + g y) x = waveDeriv v f x + waveDeriv v g x := by
  simp [waveDeriv, fderiv_fun_add hf hg]

theorem waveDeriv_const_mul (v : E) (c : ℂ) (f : E → ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    waveDeriv v (fun y => c * f y) x = c * waveDeriv v f x := by
  unfold waveDeriv
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  rfl

theorem contDiff_waveDeriv (v : E) (f : E → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (waveDeriv v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem waveDeriv_exp (v : E) (S : E → ℂ) (t : ℂ) (x : E)
    (hS : DifferentiableAt ℝ S x) :
    waveDeriv v (fun y => Complex.exp (t * S y)) x =
      Complex.exp (t * S x) * t * waveDeriv v S x := by
  have hd := ((hS.hasFDerivAt.const_mul t).cexp).fderiv
  dsimp only [waveDeriv]
  rw [hd]
  simp only [smul_apply, smul_eq_mul]
  ring

def waveCoordinateOperator (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (f : E → ℂ) (x : E) : ℂ :=
  (∑ i, ∑ j, G i j x * waveDeriv (e i) (waveDeriv (e j) f) x) +
    ∑ i, b i x * waveDeriv (e i) f x

def waveGradientPair (e : ι → E) (G : ι → ι → E → ℂ)
    (f g : E → ℂ) (x : E) : ℂ :=
  ∑ i, ∑ j, G i j x * waveDeriv (e i) f x * waveDeriv (e j) g x

theorem waveSecondDeriv_exp_mul (v w : E) (S V : E → ℂ) (t : ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) (x : E) :
    waveDeriv v (waveDeriv w (fun y => Complex.exp (t * S y) * V y)) x =
      Complex.exp (t * S x) *
        (t ^ 2 * waveDeriv v S x * waveDeriv w S x * V x +
          t * waveDeriv v (waveDeriv w S) x * V x +
          t * waveDeriv w S x * waveDeriv v V x +
          t * waveDeriv v S x * waveDeriv w V x +
          waveDeriv v (waveDeriv w V) x) := by
  have hSd := hS.differentiable (by simp)
  have hVd := hV.differentiable (by simp)
  have hE : ContDiff ℝ ∞ (fun y => Complex.exp (t * S y)) := (contDiff_const.mul hS).cexp
  have hEd := hE.differentiable (by simp)
  have hSw := (contDiff_waveDeriv w S hS).differentiable (by simp)
  have hVw := (contDiff_waveDeriv w V hV).differentiable (by simp)
  have eq : waveDeriv w (fun y => Complex.exp (t * S y) * V y) =
      fun y => Complex.exp (t * S y) * (t * waveDeriv w S y * V y + waveDeriv w V y) := by
    funext y
    rw [waveDeriv_mul _ _ _ _ (hEd y) (hVd y), waveDeriv_exp _ _ _ _ (hSd y)]
    ring
  rw [eq, waveDeriv_mul v _ (fun y => t * waveDeriv w S y * V y + waveDeriv w V y) x (hEd x)
    ((((hSw x).const_mul t).mul (hVd x)).add (hVw x)),
    waveDeriv_exp _ _ _ _ (hSd x),
    waveDeriv_add v (fun y => t * waveDeriv w S y * V y) (waveDeriv w V) x
      (((hSw x).const_mul t).mul (hVd x)) (hVw x),
    waveDeriv_mul v (fun y => t * waveDeriv w S y) V x ((hSw x).const_mul t) (hVd x),
    waveDeriv_const_mul _ _ _ _ (hSw x)]
  ring

theorem waveCoordinateOperator_exp_mul (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (S V : E → ℂ) (t : ℂ)
    (hS : ContDiff ℝ ∞ S) (hV : ContDiff ℝ ∞ V) (x : E) :
    waveCoordinateOperator e G b (fun y => Complex.exp (t * S y) * V y) x =
      Complex.exp (t * S x) *
        ((t ^ 2 * waveGradientPair e G S S x + t * waveCoordinateOperator e G b S x) * V x +
          t * (waveGradientPair e G V S x + waveGradientPair e G S V x) +
          waveCoordinateOperator e G b V x) := by
  have hSd := hS.differentiable (by simp)
  have hVd := hV.differentiable (by simp)
  have hEd : Differentiable ℝ (fun y => Complex.exp (t * S y)) :=
    ((contDiff_const.mul hS).cexp).differentiable (by simp)
  simp only [waveCoordinateOperator, waveGradientPair,
    waveSecondDeriv_exp_mul _ _ S V t hS hV x,
    waveDeriv_mul _ _ _ _ (hEd x) (hVd x), waveDeriv_exp _ _ _ _ (hSd x)]
  simp only [mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm]
  abel

end WaveDifferentiation


theorem gaussianEnvelope_moment (q : ℕ) (c : ℝ) (hc : 0 < c) (s : ℝ) (hs : 0 ≤ s) :
    s ^ q * Real.exp (s - c * s ^ 2) ≤ (q.factorial : ℝ) * Real.exp (c⁻¹) := by
  have hfac : (0 : ℝ) < q.factorial := by positivity
  have hp : s ^ q ≤ Real.exp s * q.factorial :=
    (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp s hs q)
  have hquad : 2 * s - c * s ^ 2 ≤ c⁻¹ := by
    have h := mul_nonneg hc.le (sq_nonneg (s - c⁻¹))
    have heq : c * (s - c⁻¹) ^ 2 = c * s ^ 2 - 2 * s + c⁻¹ := by
      field_simp
      ring
    rw [heq] at h
    linarith
  calc
    s ^ q * Real.exp (s - c * s ^ 2) ≤
        (Real.exp s * q.factorial) * Real.exp (s - c * s ^ 2) := by
      exact mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = (q.factorial : ℝ) * Real.exp (2 * s - c * s ^ 2) := by
      rw [show 2 * s - c * s ^ 2 = s + (s - c * s ^ 2) by ring, Real.exp_add]
      ring
    _ ≤ (q.factorial : ℝ) * Real.exp (c⁻¹) := by gcongr

theorem gaussianEnvelope_scaled_moment (q : ℕ) (c : ℝ) (hc : 0 < c)
    (n : ℝ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r) :
    r ^ q * Real.exp (Real.sqrt n * r - c * n * r ^ 2) ≤
      (q.factorial : ℝ) * Real.exp (c⁻¹) / (Real.sqrt n) ^ q := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  apply (le_div_iff₀ (pow_pos hs q)).2
  have h := gaussianEnvelope_moment q c hc (Real.sqrt n * r) (mul_nonneg hs.le hr)
  have hsq := Real.sq_sqrt hn.le
  calc
    _ = (Real.sqrt n * r) ^ q * Real.exp (Real.sqrt n * r - c * (Real.sqrt n * r) ^ 2) := by
      simp only [mul_pow, hsq]
      ring_nf
    _ ≤ _ := h

end YauCounterexamples

end

end OAI
