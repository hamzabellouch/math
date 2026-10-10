import Mathlib
import OAI.Analysis.AffineBernstein.LogBarrierCalculus

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section PositiveMatrixTraceBound
open scoped MatrixOrder

lemma posSemidef_quadratic_le_trace_mul_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (p : ι → ℝ) :
    p ⬝ᵥ A.mulVec p ≤ A.trace * ∑ i, (p i)^2 := by
  let S := CFC.sqrt A
  have hS : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp
    (show S.IsHermitian from (CFC.sqrt_nonneg A).isSelfAdjoint)
  have hSS : S*S = A := by
    simpa only [pow_two] using CFC.sq_sqrt A hA.nonneg
  have hvec : Matrix.vecMul p S = Matrix.mulVec S p := by
    rw [← Matrix.mulVec_transpose,hS.eq]
  have hm : p ⬝ᵥ A.mulVec p = ∑ i, (S.mulVec p i)^2 := by
    rw [← hSS, ← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,hvec]
    simp only [dotProduct,pow_two]
  have ht : A.trace = ∑ i, ∑ j, (S i j)^2 := by
    rw [← hSS]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hS.apply i j]
    ring
  rw [hm,ht,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [Matrix.mulVec, dotProduct] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => S i j) p

end PositiveMatrixTraceBound

def gradientSquared {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ k, (dirDeriv (coordinateVector n k) u x)^2

def gradientHessianSquare {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ k, dirDeriv (coordinateVector n k) u x * dirDeriv (coordinateVector n k) (gradientEnergy u) x

lemma gradientSquared_nonneg {n : ℕ} (u : Space n → ℝ) (x : Space n) :
    0 ≤ gradientSquared u x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma inverseHessianPair_gradient_self {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) :
    inverseHessianPair u (gradientEnergy u) u x = gradientSquared u x := by
  rw [inverseHessian_pair_gradient hu hp]
  simp only [gradientSquared,pow_two]

lemma gradientHessianSquare_eq_dotProduct {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) : gradientHessianSquare u x =
      (fun i => dirDeriv (coordinateVector n i) u x) ⬝ᵥ
        (hessian u x).mulVec (fun i => dirDeriv (coordinateVector n i) u x) := by
  simp only [gradientHessianSquare,dirDeriv_gradientEnergy hu,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma gradientHessianSquare_nonneg {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) :
    0 ≤ gradientHessianSquare u x := by
  rw [gradientHessianSquare_eq_dotProduct hu]
  simpa using hp.posSemidef.dotProduct_mulVec_nonneg (fun i => dirDeriv (coordinateVector n i) u x)

lemma gradientHessianSquare_le_trace {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) :
    gradientHessianSquare u x ≤ (hessian u x).trace * gradientSquared u x := by
  rw [gradientHessianSquare_eq_dotProduct hu]
  exact posSemidef_quadratic_le_trace_mul_sq hp.posSemidef _

lemma inverseHessianPair_grad_linear {n : ℕ} {u f g h : Space n → ℝ} {x : Space n}
    (hp : (hessian u x).PosDef) (k l : ℝ)
    (he : ∀ i : Fin n, dirDeriv (coordinateVector n i) h x =
      k * dirDeriv (coordinateVector n i) f x + l * dirDeriv (coordinateVector n i) g x) :
    inverseHessianPair u h h x = k^2 * inverseHessianPair u f f x +
      2*k*l*inverseHessianPair u g f x + l^2 * inverseHessianPair u g g x := by
  have hh : inverseHessianPair u h h x = k^2 * inverseHessianPair u f f x +
      k*l*inverseHessianPair u f g x + k*l*inverseHessianPair u g f x +
      l^2 * inverseHessianPair u g g x := by
    unfold inverseHessianPair
    simp only [he,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [inverseHessianPair_symm hp (f := f) (g := g)] at hh
  rw [hh]
  ring

lemma affineDetBarrier_critical_gradient {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (hn : u x ≠ 0)
    (β γ : ℝ) (hm : IsLocalMax (affineDetBarrier u β γ) x) (i : Fin n) :
    dirDeriv (coordinateVector n i) (logHessianDet u) x =
      (-β / u x) * dirDeriv (coordinateVector n i) u x +
        (-γ) * dirDeriv (coordinateVector n i) (gradientEnergy u) x := by
  have hz : dirDeriv (coordinateVector n i) (affineDetBarrier u β γ) x = 0 := by
    simp only [dirDeriv,hm.fderiv_eq_zero,zero_apply]
  rw [dirDeriv_affineDetBarrier hu hp hn] at hz
  linear_combination (norm := ring_nf) hz

lemma inverseHessianPair_logHessianDet_of_barrier_max {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (hn : u x ≠ 0)
    (β γ : ℝ) (hm : IsLocalMax (affineDetBarrier u β γ) x) :
    inverseHessianPair u (logHessianDet u) (logHessianDet u) x =
      β^2 / (u x)^2 * inverseHessianPair u u u x +
        (2*β*γ/u x) * gradientSquared u x + γ^2 * gradientHessianSquare u x := by
  rw [inverseHessianPair_grad_linear hp (-β/u x) (-γ)
    (affineDetBarrier_critical_gradient hu hp hn β γ hm),
    inverseHessianPair_gradient_self hu hp,inverseHessian_pair_gradient hu hp]
  change (-β/u x)^2 * _ + 2*(-β/u x)*(-γ)*_ + (-γ)^2 * gradientHessianSquare u x = _
  ring

lemma gradient_logHessianDet_of_barrier_max {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (hn : u x ≠ 0)
    (β γ : ℝ) (hm : IsLocalMax (affineDetBarrier u β γ) x) :
    (∑ k, dirDeriv (coordinateVector n k) u x * dirDeriv (coordinateVector n k) (logHessianDet u) x) =
      (-β/u x) * gradientSquared u x - γ * gradientHessianSquare u x := by
  simp only [affineDetBarrier_critical_gradient hu hp hn β γ hm,
    gradientSquared,gradientHessianSquare,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The unabridged differential barrier identity at a local maximum. Its
coefficient is the original affine maximal exponent. -/
lemma affineDetBarrier_peak_identity {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hneg : ∀ x ∈ Ω, u x < 0) {x : Space n} (hx : x ∈ Ω) (γ : ℝ)
    (hmax : IsLocalMax (affineDetBarrier u ((n:ℝ)+2) γ) x) :
    inverseHessianTrace u (affineDetBarrier u ((n:ℝ)+2) γ) x =
      ((n:ℝ)*((n:ℝ)+2)/(u x)^2) * inverseHessianPair u u u x +
      γ * (hessian u x).trace - γ^2/((n:ℝ)+2) * gradientHessianSquare u x +
      ((n:ℝ)*((n:ℝ)+2) + γ*(n:ℝ)*gradientSquared u x) / u x := by
  have hu' := hu.contDiffAt (hΩ.mem_nhds hx)
  have hn : u x ≠ 0 := ne_of_lt (hneg x hx)
  have hd : (n:ℝ)+2 ≠ 0 := by positivity
  rw [inverseHessianTrace_affineDetBarrier hΩ hu hp hm hneg hx,
    inverseHessianPair_logHessianDet_of_barrier_max hu' (hp x hx) hn _ γ hmax,
    gradient_logHessianDet_of_barrier_max hu' (hp x hx) hn _ γ hmax]
  field_simp
  ring

end AffineBernstein

end

end OAI
