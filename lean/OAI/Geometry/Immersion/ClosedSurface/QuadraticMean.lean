import OAI.Geometry.Immersion.ClosedSurface.OscillatoryModel
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds
import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

abbrev Base := ℝ × ℝ
abbrev CVec (n : ℕ) := Fin n → ℂ
abbrev RVec (n : ℕ) := Fin n → ℝ

def realPart {n : ℕ} (Z : CVec n) : RVec n := fun i => (Z i).re

def conjugate {n : ℕ} (Z : CVec n) : CVec n := fun i => star (Z i)

def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * I)

def realMode {n : ℕ} (θ : ℝ) (Z : CVec n) : RVec n := realPart (phase θ • Z)

lemma phase_add (θ ψ : ℝ) : phase (θ + ψ) = phase θ * phase ψ := by
  simp only [phase, ofReal_add, add_mul, Complex.exp_add]

lemma phase_conj (θ : ℝ) : star (phase θ) = phase (-θ) := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, ofReal_neg]
  congr 1
  ring

lemma phase_sub (θ ψ : ℝ) : phase (θ - ψ) = phase θ * star (phase ψ) := by
  rw [phase_conj, ← phase_add, sub_eq_add_neg]

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma real_product (a b : ℂ) : a.re * b.re = ((a * star b).re + (a * b).re) / 2 := by
  simp only [Complex.star_def, mul_re, conj_re, conj_im]
  ring

lemma mode_product (θ ψ : ℝ) (a b : ℂ) :
    (phase θ * a).re * (phase ψ * b).re =
      ((phase (θ - ψ) * (a * star b)).re + (phase (θ + ψ) * (a * b)).re) / 2 := by
  rw [real_product, phase_sub, phase_add]
  simp only [Complex.star_def, map_mul]
  congr 2 <;> congr 1 <;> ring



theorem realMode_dot {n : ℕ} (θ ψ : ℝ) (A B : CVec n) :
    realMode θ A ⬝ᵥ realMode ψ B =
      ((phase (θ - ψ) * (A ⬝ᵥ conjugate B)).re +
        (phase (θ + ψ) * (A ⬝ᵥ B)).re) / 2 := by
  unfold realMode realPart dotProduct conjugate
  simp only [Pi.smul_apply, smul_eq_mul, mode_product, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]




theorem realMode_self_phase {n : ℕ} (θ : ℝ) (A B : CVec n) :
    realMode θ A ⬝ᵥ realMode θ B =
      (A ⬝ᵥ conjugate B).re / 2 + (phase (2 * θ) * (A ⬝ᵥ B)).re / 2 := by
  rw [realMode_dot, sub_self, phase_zero, one_mul]
  have h : θ + θ = 2 * θ := by ring
  rw [h, add_div]



def derivativeAmplitude {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (Z : Base → CVec n)
    (v : Base) (p : Base) : CVec n :=
  fderiv ℝ Z p v + (I / (τ : ℂ) * (fderiv ℝ φ p v : ℂ)) • Z p


def displacement {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (Z : Base → CVec n) : Base → RVec n :=
  fun p => realMode (φ p / τ) (Z p)

def realPartCLM (n : ℕ) : CVec n →L[ℝ] RVec n :=
  ContinuousLinearMap.pi fun i => Complex.reCLM.comp (ContinuousLinearMap.proj i)

lemma realPartCLM_apply {n : ℕ} (Z : CVec n) : realPartCLM n Z = realPart Z := rfl

lemma phase_comp_hasFDerivAt {φ : Base → ℝ} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (τ : ℝ) :
    HasFDerivAt (fun q => phase (φ q / τ))
      (phase (φ p / τ) • ((I / (τ : ℂ)) • (Complex.ofRealCLM.comp (fderiv ℝ φ p)))) p := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp p hφ.hasFDerivAt).const_mul
    (I / (τ : ℂ))).cexp
  have he (q : Base) : phase (φ q / τ) = Complex.exp (I / (τ : ℂ) * (φ q : ℂ)) := by
    simp only [phase, ofReal_div]
    congr 1
    ring
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, he] using h

lemma derivative_displacement {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v : Base) :
    fderiv ℝ (displacement τ φ Z) p v =
      realMode (φ p / τ) (derivativeAmplitude τ φ Z v p) := by
  have hc := ((phase_comp_hasFDerivAt hφ τ).fun_smul hZ.hasFDerivAt)
  have hr := (realPartCLM n).hasFDerivAt.comp p hc
  simp only [Function.comp_def] at hr
  rw [show displacement τ φ Z = fun q => realPartCLM n (phase (φ q / τ) • Z q) from rfl,
    hr.fderiv]
  ext i
  simp only [realPartCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    Complex.reCLM_apply, ContinuousLinearMap.proj_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    Complex.ofRealCLM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    realMode, realPart, derivativeAmplitude]
  congr 1
  ring



def zeroPair {n : ℕ} (A B : CVec n) : ℝ := (A ⬝ᵥ conjugate B).re / 2

def doublePair {n : ℕ} (θ : ℝ) (A B : CVec n) : ℝ :=
  (phase (2 * θ) * (A ⬝ᵥ B)).re / 2

def crossPair {n : ℕ} (θ ψ : ℝ) (A B : CVec n) : ℝ :=
  ((phase (θ - ψ) * (A ⬝ᵥ conjugate B)).re +
    (phase (θ + ψ) * (A ⬝ᵥ B)).re) / 2




theorem finite_phase_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (A B : ι → CVec n) :
    (∑ i, realMode (θ i) (A i)) ⬝ᵥ (∑ i, realMode (θ i) (B i)) =
      (∑ i, zeroPair (A i) (B i)) + (∑ i, doublePair (θ i) (A i) (B i)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, crossPair (θ i) (θ j) (A i) (B j) := by
  simp only [sum_dotProduct, dotProduct_sum]
  have hi (i : ι) :
      ∑ j, realMode (θ i) (A i) ⬝ᵥ realMode (θ j) (B j) =
        zeroPair (A i) (B i) + doublePair (θ i) (A i) (B i) +
          ∑ j ∈ Finset.univ.erase i, crossPair (θ i) (θ j) (A i) (B j) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i), realMode_self_phase]
    simp only [realMode_dot, crossPair, zeroPair, doublePair]
    ring
  rw [Finset.sum_comm]
  simp only [hi, Finset.sum_add_distrib]

lemma differentiableAt_displacement {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) :
    DifferentiableAt ℝ (displacement τ φ Z) p :=
  ((realPartCLM n).hasFDerivAt.comp p
    ((phase_comp_hasFDerivAt hφ τ).fun_smul hZ.hasFDerivAt)).differentiableAt

def sumDisplacement {n : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → Base → CVec n) : Base → RVec n :=
  fun p => ∑ i, displacement τ (φ i) (Z i) p

def quadraticMetric {n : ℕ} (U : Base → RVec n) (v w p : Base) : ℝ :=
  fderiv ℝ U p v ⬝ᵥ fderiv ℝ U p w

def meanMetric {n : ℕ} {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (Z : ι → Base → CVec n) (v w p : Base) : ℝ :=
  ∑ i, zeroPair (derivativeAmplitude τ (φ i) (Z i) v p)
    (derivativeAmplitude τ (φ i) (Z i) w p)



theorem quadraticMetric_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) {φ : ι → Base → ℝ} {Z : ι → Base → CVec n} {p : Base}
    (hφ : ∀ i, DifferentiableAt ℝ (φ i) p) (hZ : ∀ i, DifferentiableAt ℝ (Z i) p)
    (v w : Base) :
    quadraticMetric (sumDisplacement τ φ Z) v w p = meanMetric τ φ Z v w p +
      (∑ i, doublePair (φ i p / τ) (derivativeAmplitude τ (φ i) (Z i) v p)
        (derivativeAmplitude τ (φ i) (Z i) w p)) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        crossPair (φ i p / τ) (φ j p / τ) (derivativeAmplitude τ (φ i) (Z i) v p)
          (derivativeAmplitude τ (φ j) (Z j) w p) := by
  have hd (v : Base) : fderiv ℝ (sumDisplacement τ φ Z) p v =
      ∑ i, realMode (φ i p / τ) (derivativeAmplitude τ (φ i) (Z i) v p) := by
    unfold sumDisplacement
    rw [fderiv_fun_sum (fun i _ => differentiableAt_displacement (hφ i) (hZ i) τ)]
    simp only [sum_apply, derivative_displacement (hφ _) (hZ _)]
  rw [quadraticMetric, hd v, hd w, finite_phase_expansion]
  rfl


def leadingAmplitude {n : ℕ} (δ b ξ : ℝ) (N : RVec n) : CVec n :=
  fun j => I * ((Real.sqrt 2 * δ * b * ξ * N j : ℝ) : ℂ)

lemma leadingAmplitude_zeroPair {n : ℕ} (δ b ξ ζ : ℝ) (N : RVec n)
    (hN : N ⬝ᵥ N = 1) :
    zeroPair (leadingAmplitude δ b ξ N) (leadingAmplitude δ b ζ N) =
      δ ^ 2 * b ^ 2 * ξ * ζ := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold zeroPair dotProduct conjugate leadingAmplitude
  simp only [Complex.star_def, map_mul, conj_I, conj_ofReal, Complex.re_sum,
    mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, mul_zero,
    zero_sub, sub_zero, zero_add, one_mul, neg_re, neg_im, neg_zero]
  have he (j : Fin n) :
      -(Real.sqrt 2 * δ * b * ξ * N j * -(Real.sqrt 2 * δ * b * ζ * N j)) =
        (2 * δ ^ 2 * b ^ 2 * ξ * ζ) * (N j * N j) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * δ ^ 2 * b ^ 2 * ξ * ζ * (N j * N j) := by ring
      _ = _ := by rw [hs]
  simp only [neg_one_mul, he, ← Finset.mul_sum]
  change 2 * δ ^ 2 * b ^ 2 * ξ * ζ * (N ⬝ᵥ N) / 2 = _
  rw [hN]
  ring

end ClosedSurfaceR4.QuadraticMean

end

end OAI
