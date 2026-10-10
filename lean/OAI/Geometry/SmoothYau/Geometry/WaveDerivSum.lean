import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.WaveDeriv

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
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι α : Type*} [Fintype ι]

theorem waveDeriv_sum (s : Finset α) (v : E) (f : α → E → ℂ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (x : E) :
    waveDeriv v (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, waveDeriv v (f i) x := by
  simp only [waveDeriv, fderiv_fun_sum (fun i hi => (hf i hi).differentiable (by simp) x),
    sum_apply]

theorem waveCoordinateOperator_sum (s : Finset α) (e : ι → E)
    (G : ι → ι → E → ℂ) (b : ι → E → ℂ) (f : α → E → ℂ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) (x : E) :
    waveCoordinateOperator e G b (fun y => ∑ i ∈ s, f i y) x =
      ∑ i ∈ s, waveCoordinateOperator e G b (f i) x := by
  have hd (v : E) : waveDeriv v (fun y => ∑ i ∈ s, f i y) =
      fun y => ∑ i ∈ s, waveDeriv v (f i) y := funext (fun y => waveDeriv_sum s v f hf y)
  simp only [waveCoordinateOperator, hd]
  simp only [waveDeriv_sum s _ _ (fun i hi => contDiff_waveDeriv _ (f i) (hf i hi)), Finset.mul_sum,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (s:=Finset.univ) (t:=s)]
  congr 1
  simp only [Finset.sum_comm (s:=Finset.univ) (t:=s)]

theorem waveCoordinateOperator_const_mul (e : ι → E)
    (G : ι → ι → E → ℂ) (b : ι → E → ℂ) (c : ℂ) (f : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (x : E) :
    waveCoordinateOperator e G b (fun y => c * f y) x =
      c * waveCoordinateOperator e G b f x := by
  have hd (v : E) : waveDeriv v (fun y => c * f y) = fun y => c * waveDeriv v f y :=
    funext (fun y => waveDeriv_const_mul v c f y (hf.differentiable (by simp) y))
  simp only [waveCoordinateOperator, hd, waveDeriv_const_mul _ _ _ _
    ((contDiff_waveDeriv _ _ hf).differentiable (by simp) x), mul_add,
    Finset.mul_sum, mul_left_comm]

theorem finite_transport_telescope (n : ℂ) (hn : n ≠ 0)
    (t d r : ℕ → ℂ) (h0 : r 0 = t 0)
    (hs : ∀ j, r (j+1) = t (j+1) + d j) (J : ℕ) :
    n * (∑ j ∈ Finset.range (J+1), (n⁻¹)^j * t j) +
      (∑ j ∈ Finset.range (J+1), (n⁻¹)^j * d j) =
    n * (∑ j ∈ Finset.range (J+1), (n⁻¹)^j * r j) + (n⁻¹)^J * d J := by
  induction J with
  | zero => simp [h0]
  | succ J ih =>
    have hp : n * (n⁻¹)^(J+1) = (n⁻¹)^J := by rw [pow_succ]; field_simp
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [hs]
    linear_combination ih - d J * hp

def finiteWaveTransport (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (S V : E → ℂ) (x : E) : ℂ :=
  waveGradientPair e G V S x + waveGradientPair e G S V x +
    (waveCoordinateOperator e G b S x + 2) * V x

theorem finite_wave_residual (e : ι → E) (G : ι → ι → E → ℂ)
    (b : ι → E → ℂ) (S : E → ℂ) (hS : ContDiff ℝ ∞ S)
    (V : ℕ → E → ℂ) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (R : ℕ → E → ℂ) (hR0 : R 0 = finiteWaveTransport e G b S (V 0))
    (hRs : ∀ j, R (j+1) = fun x => finiteWaveTransport e G b S (V (j+1)) x +
      waveCoordinateOperator e G b (V j) x)
    (n : ℂ) (hn : n ≠ 0) (J : ℕ) (x : E) :
    let A := fun y => ∑ j ∈ Finset.range (J+1), (n⁻¹)^j * V j y
    waveCoordinateOperator e G b (fun y => Complex.exp (n*S y) * A y) x +
      n*(n+2) * (Complex.exp (n*S x) * A x) =
    Complex.exp (n*S x) *
      (n^2 * (1 + waveGradientPair e G S S x) * A x +
        n * (∑ j ∈ Finset.range (J+1), (n⁻¹)^j * R j x) +
        (n⁻¹)^J * waveCoordinateOperator e G b (V J) x) := by
  dsimp only
  have heq : (fun y => Complex.exp (n*S y) *
      ∑ j ∈ Finset.range (J+1), (n⁻¹)^j * V j y) =
      fun y => ∑ j ∈ Finset.range (J+1), (n⁻¹)^j *
        (Complex.exp (n*S y) * V j y) := by
    funext y
    simp only [Finset.mul_sum]
    congr 1
    funext j
    ring
  have hEV (j : ℕ) : ContDiff ℝ ∞ (fun y => Complex.exp (n*S y) * V j y) :=
    ((contDiff_const.mul hS).cexp).mul (hV j)
  rw [heq, waveCoordinateOperator_sum _ _ _ _ _ (fun j _ => contDiff_const.mul (hEV j))]
  simp only [waveCoordinateOperator_const_mul _ _ _ _ _ (hEV _), waveCoordinateOperator_exp_mul _ _ _ _ _ _ hS (hV _)]
  have ht := finite_transport_telescope n hn
    (fun j => finiteWaveTransport e G b S (V j) x)
    (fun j => waveCoordinateOperator e G b (V j) x) (fun j => R j x)
    (congrFun hR0 x) (fun j => congrFun (hRs j) x) J
  dsimp only [finiteWaveTransport] at ht
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul] at ht ⊢
  linear_combination (norm := skip) Complex.exp (n*S x) * ht
  ring_nf
  simp only [Finset.mul_sum]
  ring_nf

end YauCounterexamples

end

end OAI
