import Mathlib
import OAI.Geometry.SmoothYau.Estimates.CoefficientElliptic
import OAI.Geometry.SmoothYau.Estimates.QuadraticInnerSpace

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def coefficientTransport (X : ι → SmoothScalar E) (p : SmoothScalar E) : SmoothScalar E :=
  ∑ i, X i * SmoothScalar.directional (e i) p

def carlemanSymmetric (a : ι → ι → SmoothScalar E) (p : SmoothScalar E) (τ : ℝ) :
    EllipticTest K →ₗ[ℝ] EllipticTest K :=
  testElliptic K e a + τ^2 • testMultiply K p

def carlemanSkew (X : ι → SmoothScalar E) (τ : ℝ) :
    EllipticTest K →ₗ[ℝ] EllipticTest K :=
  (-τ) • testSkewTransport K e X

lemma testMultiplier_skew_pair (X : ι → SmoothScalar E) (p : SmoothScalar E)
    (f : EllipticTest K) :
    testPair K (testMultiply K p f) (testSkewTransport K e X f) =
      -weightedPair K (coefficientTransport e X p) f f := by
  have h (i : ι) := weightedPair_self_derivative K (p * X i) (e i) f
  simp only [SmoothScalar.directional_mul, weightedPair_add_coeff] at h
  simp only [testSkewTransport, LinearMap.add_apply, LinearMap.smul_apply,
    testPair_add_right, testPair_smul_right, testTransport, LinearMap.sum_apply,
    LinearMap.comp_apply, testPair_sum_right]
  change 2 * (∑ i, weightedPair K p f (testMultiply K (X i) (testDerivative K (e i) f))) +
    weightedPair K p f (testMultiply K (coefficientDivergence e X) f) = _
  simp only [weightedPair_mul, coefficientDivergence, Finset.mul_sum,
    weightedPair_sum_coeff, coefficientTransport]
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (X i)]
  linarith [h i]

lemma derivative_product_energy (a : ι → ι → SmoothScalar E) (X : ι → SmoothScalar E)
    (f : EllipticTest K) :
    (∑ i, ∑ j, ∑ k, weightedPair K (SmoothScalar.directional (e k) (a i j * X k))
        (testDerivative K (e j) f) (testDerivative K (e i) f)) =
      (∑ i, ∑ j, ∑ k, weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
        (testDerivative K (e j) f) (testDerivative K (e i) f)) +
      ∑ i, ∑ j, weightedPair K (a i j * coefficientDivergence e X)
        (testDerivative K (e j) f) (testDerivative K (e i) f) := by
  simp only [SmoothScalar.directional_mul, weightedPair_add_coeff,
    Finset.sum_add_distrib, coefficientDivergence, Finset.mul_sum, weightedPair_sum_coeff]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]

theorem carleman_commutator (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (X : ι → SmoothScalar E) (p : SmoothScalar E)
    (τ : ℝ) (f : EllipticTest K) :
    2 * testPair K (carlemanSymmetric K e a p τ f) (carlemanSkew K e X τ f) =
      τ * (4 * (∑ i, ∑ j, ∑ k,
          weightedPair K (a i j * SmoothScalar.directional (e i) (X k))
            (testDerivative K (e j) f) (testDerivative K (e k) f)) -
        2 * (∑ i, ∑ j, ∑ k,
          weightedPair K (X k * SmoothScalar.directional (e k) (a i j))
            (testDerivative K (e j) f) (testDerivative K (e i) f)) -
        weightedPair K (coefficientElliptic e a (coefficientDivergence e X)) f f) +
      2 * τ^3 * weightedPair K (coefficientTransport e X p) f f := by
  have hT := testElliptic_transport_pair K e a ha X f
  have hq := testElliptic_multiplier_pair K e a ha (coefficientDivergence e X) f
  have hp := testMultiplier_skew_pair K e X p f
  rw [derivative_product_energy K e a X f] at hT
  simp only [carlemanSymmetric, carlemanSkew, LinearMap.add_apply, LinearMap.smul_apply,
    testPair_smul_right, testPair_add_left, testPair_smul_left, hp]
  simp only [testSkewTransport, LinearMap.add_apply, LinearMap.smul_apply,
    testPair_add_right, testPair_smul_right]
  linear_combination -τ * (2 * hT + hq)

lemma testPair_cauchy_shift (f g : EllipticTest K) (c : ℝ) :
    -2 * c * testPair K f g - c^2 * testPair K g g ≤ testPair K f f := by
  have h := testPair_nonneg K (f + c • g)
  simp only [testPair_add_left, testPair_add_right, testPair_smul_left,
    testPair_smul_right, testPair_comm K g f] at h
  nlinarith


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

lemma SmoothScalar.sum_apply {κ : Type*} (s : Finset κ) (f : κ → SmoothScalar E) (x : E) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Subalgebra.coe_zero, Pi.zero_apply]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Subalgebra.coe_add, Pi.add_apply, ih]

def coefficientGradient (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) :
    ι → SmoothScalar E := fun i => ∑ j, a i j * SmoothScalar.directional (e j) φ

def coefficientNorm (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) : SmoothScalar E :=
  ∑ i, SmoothScalar.directional (e i) φ * coefficientGradient e a φ i

def convexifyPhase (ψ : SmoothScalar E) (H : ℝ) : SmoothScalar E :=
  ψ + (H/2) • (ψ*ψ)

lemma phase_derivative (ψ : SmoothScalar E) (H : ℝ) (v : E) :
    SmoothScalar.directional v (convexifyPhase ψ H) =
      (1 + H • ψ) * SmoothScalar.directional v ψ := by
  simp only [convexifyPhase, map_add, map_smul, SmoothScalar.directional_mul]
  apply Subtype.ext
  ext x
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Subalgebra.coe_one,
    Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
  ring

lemma phase_gradient (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ) (i : ι) :
    coefficientGradient e a (convexifyPhase ψ H) i =
      (1 + H • ψ) * coefficientGradient e a ψ i := by
  simp only [coefficientGradient, phase_derivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma phase_norm (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ) :
    coefficientNorm e a (convexifyPhase ψ H) =
      (1 + H • ψ)^2 * coefficientNorm e a ψ := by
  simp only [coefficientNorm, phase_derivative, phase_gradient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma SmoothScalar.directional_one (v : E) : SmoothScalar.directional v (1 : SmoothScalar E) = 0 := by
  apply Subtype.ext
  ext x
  simp [SmoothScalar.directional_apply]

lemma phase_gradient_at (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ)
    (x : E) (hx : ψ x = 0) (i : ι) :
    coefficientGradient e a (convexifyPhase ψ H) i x = coefficientGradient e a ψ i x := by
  rw [phase_gradient]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul,
    Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, hx,
    mul_zero, add_zero, one_mul]

lemma phase_norm_at (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ)
    (x : E) (hx : ψ x = 0) :
    coefficientNorm e a (convexifyPhase ψ H) x = coefficientNorm e a ψ x := by
  rw [phase_norm]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul,
    Subalgebra.coe_pow, Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
    Pi.pow_apply, smul_eq_mul, hx, mul_zero, add_zero, one_pow, one_mul]

lemma phase_gradient_derivative_at (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ)
    (x : E) (hx : ψ x = 0) (i j : ι) :
    SmoothScalar.directional (e j) (coefficientGradient e a (convexifyPhase ψ H) i) x =
      SmoothScalar.directional (e j) (coefficientGradient e a ψ i) x +
        H * SmoothScalar.directional (e j) ψ x * coefficientGradient e a ψ i x := by
  rw [phase_gradient, SmoothScalar.directional_mul, map_add, map_smul,
    SmoothScalar.directional_one]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul,
    Subalgebra.coe_zero, Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul, hx]
  ring

lemma phase_transport_norm_at (a : ι → ι → SmoothScalar E) (ψ : SmoothScalar E) (H : ℝ)
    (x : E) (hx : ψ x = 0) :
    coefficientTransport e (coefficientGradient e a (convexifyPhase ψ H))
        (coefficientNorm e a (convexifyPhase ψ H)) x =
      coefficientTransport e (coefficientGradient e a ψ) (coefficientNorm e a ψ) x +
        2*H*(coefficientNorm e a ψ x)^2 := by
  have hd (i : ι) :
      SmoothScalar.directional (e i) (coefficientNorm e a (convexifyPhase ψ H)) x =
        SmoothScalar.directional (e i) (coefficientNorm e a ψ) x +
          2*H*SmoothScalar.directional (e i) ψ x * coefficientNorm e a ψ x := by
    rw [phase_norm, pow_two, SmoothScalar.directional_mul, SmoothScalar.directional_mul,
      map_add, map_smul, SmoothScalar.directional_one]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul,
      Subalgebra.coe_zero, Pi.mul_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul, hx]
    ring
  simp only [coefficientTransport, SmoothScalar.sum_apply,
    Subalgebra.coe_mul, Pi.mul_apply, phase_gradient_at e a ψ H x hx, hd,
    mul_add, Finset.sum_add_distrib]
  congr 1
  have hn : coefficientNorm e a ψ x =
      ∑ i, SmoothScalar.directional (e i) ψ x * coefficientGradient e a ψ i x := by
    simp only [coefficientNorm, SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]
  calc
    _ = 2*H*(∑ i, SmoothScalar.directional (e i) ψ x * coefficientGradient e a ψ i x) *
        coefficientNorm e a ψ x := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← hn]; ring


end

section
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Compacts E) {ι : Type*} [Fintype ι] (e : ι → E)

def exponentialWeight (φ : SmoothScalar E) (τ : ℝ) : SmoothScalar E :=
  ⟨fun x => Real.exp (τ * φ x), Real.contDiff_exp.comp (contDiff_const.mul (SmoothScalar.contDiff φ))⟩
@[simp] lemma exponentialWeight_apply (φ : SmoothScalar E) (τ : ℝ) (x : E) :
    exponentialWeight φ τ x = Real.exp (τ * φ x) := rfl

lemma exponentialWeight_derivative (φ : SmoothScalar E) (τ : ℝ) (v : E) :
    SmoothScalar.directional v (exponentialWeight φ τ) =
      τ • (exponentialWeight φ τ * SmoothScalar.directional v φ) := by
  apply Subtype.ext
  ext x
  change fderiv ℝ (fun y => Real.exp (τ * φ y)) x v = _
  have hd := (((SmoothScalar.contDiff φ).differentiable (by simp) x).hasFDerivAt.const_mul τ).exp
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul, Subalgebra.coe_smul, Subalgebra.coe_mul, Pi.smul_apply,
    Pi.mul_apply, SmoothScalar.directional_apply, exponentialWeight_apply]
  ring

lemma testMultiply_one (f : EllipticTest K) : testMultiply K 1 f = f := by
  ext x; simp [testMultiply_apply]

lemma testMultiply_exponential_inverse (φ : SmoothScalar E) (τ : ℝ) (f : EllipticTest K) :
    testMultiply K (exponentialWeight φ (-τ)) (testMultiply K (exponentialWeight φ τ) f) = f := by
  ext x
  simp only [testMultiply_apply, exponentialWeight_apply, ← mul_assoc, ← Real.exp_add]
  simp

lemma coefficientElliptic_exponential (a : ι → ι → SmoothScalar E) (φ : SmoothScalar E) (τ : ℝ) :
    coefficientElliptic e a (exponentialWeight φ τ) =
      exponentialWeight φ τ *
        (τ • coefficientDivergence e (coefficientGradient e a φ) +
          τ^2 • coefficientNorm e a φ) := by
  have hg (i : ι) : (∑ j, a i j * SmoothScalar.directional (e j) (exponentialWeight φ τ)) =
      τ • (exponentialWeight φ τ * coefficientGradient e a φ i) := by
    apply Subtype.ext
    ext x
    simp only [exponentialWeight_derivative, coefficientGradient, SmoothScalar.sum_apply,
      Subalgebra.coe_smul, Subalgebra.coe_mul, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : coefficientElliptic e a (exponentialWeight φ τ) =
      ∑ i, SmoothScalar.directional (e i)
        (∑ j, a i j * SmoothScalar.directional (e j) (exponentialWeight φ τ)) := by
    simp only [coefficientElliptic, map_sum]
  rw [he]
  simp_rw [hg]
  simp only [map_smul, SmoothScalar.directional_mul, exponentialWeight_derivative,
    coefficientDivergence, coefficientNorm,
    Finset.sum_add_distrib, smul_add, Finset.smul_sum, mul_add, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Subtype.ext
  ext x
  simp only [Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_mul,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

lemma testElliptic_product (a : ι → ι → SmoothScalar E) (ha : ∀ i j, a i j = a j i)
    (b : SmoothScalar E) (f : EllipticTest K) :
    testElliptic K e a (testMultiply K b f) =
      testMultiply K b (testElliptic K e a f) +
        (2:ℝ) • (∑ i, ∑ j, testMultiply K (a i j * SmoothScalar.directional (e i) b)
          (testDerivative K (e j) f)) + testMultiply K (coefficientElliptic e a b) f := by
  have hterm (i j : ι) :
      testDerivative K (e i) (testMultiply K (a i j) (testDerivative K (e j) (testMultiply K b f))) =
      testMultiply K b (testDerivative K (e i) (testMultiply K (a i j) (testDerivative K (e j) f))) +
      testMultiply K (a i j * SmoothScalar.directional (e i) b) (testDerivative K (e j) f) +
      testMultiply K (a i j * SmoothScalar.directional (e j) b) (testDerivative K (e i) f) +
      testMultiply K (SmoothScalar.directional (e i) (a i j * SmoothScalar.directional (e j) b)) f := by
    simp only [testProductRule, map_add, ← testMultiply_mul,
      SmoothScalar.directional_mul, testMultiply_add]
    ext x
    simp only [FunLike.coe_add, Pi.add_apply, testMultiply_apply,
      Subalgebra.coe_mul, Pi.mul_apply]
    ring
  have hcross : (∑ i, ∑ j, testMultiply K (a i j * SmoothScalar.directional (e j) b)
      (testDerivative K (e i) f)) =
      ∑ i, ∑ j, testMultiply K (a i j * SmoothScalar.directional (e i) b)
        (testDerivative K (e j) f) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
  simp only [testElliptic, LinearMap.sum_apply, LinearMap.comp_apply, hterm,
    Finset.sum_add_distrib, map_sum, coefficientElliptic, testMultiply_sum]
  rw [hcross]
  simp only [two_smul, add_assoc]

lemma testElliptic_exponential (a : ι → ι → SmoothScalar E) (ha : ∀ i j, a i j = a j i)
    (φ : SmoothScalar E) (τ : ℝ) (f : EllipticTest K) :
    testElliptic K e a (testMultiply K (exponentialWeight φ τ) f) =
      testMultiply K (exponentialWeight φ τ)
        (testElliptic K e a f + τ • testSkewTransport K e (coefficientGradient e a φ) f +
          τ^2 • testMultiply K (coefficientNorm e a φ) f) := by
  rw [testElliptic_product K e a ha, coefficientElliptic_exponential]
  have hcross : (∑ i, ∑ j, testMultiply K
      (a i j * SmoothScalar.directional (e i) (exponentialWeight φ τ)) (testDerivative K (e j) f)) =
      τ • testMultiply K (exponentialWeight φ τ) (testTransport K e (coefficientGradient e a φ) f) := by
    rw [Finset.sum_comm]
    simp only [exponentialWeight_derivative, testTransport, coefficientGradient,
      LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Finset.smul_sum,
      testMultiply_sum, ← testMultiply_mul, mul_smul_comm, testMultiply_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [ha j i]
    congr 2
    ring_nf
  rw [hcross]
  simp only [testMultiply_mul, testMultiply_add, testMultiply_smul, map_add, map_smul,
    testSkewTransport, LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul]
  module

lemma carleman_conjugation (a : ι → ι → SmoothScalar E) (ha : ∀ i j, a i j = a j i)
    (φ : SmoothScalar E) (τ : ℝ) (u : EllipticTest K) :
    carlemanSymmetric K e a (coefficientNorm e a φ) τ (testMultiply K (exponentialWeight φ τ) u) +
      carlemanSkew K e (coefficientGradient e a φ) τ (testMultiply K (exponentialWeight φ τ) u) =
      testMultiply K (exponentialWeight φ τ) (testElliptic K e a u) := by
  have h := testElliptic_exponential K e a ha φ (-τ) (testMultiply K (exponentialWeight φ τ) u)
  rw [testMultiply_exponential_inverse] at h
  apply_fun testMultiply K (exponentialWeight φ τ) at h
  have hi (f : EllipticTest K) :
      testMultiply K (exponentialWeight φ τ) (testMultiply K (exponentialWeight φ (-τ)) f) = f := by
    simpa only [neg_neg] using testMultiply_exponential_inverse K φ (-τ) f
  rw [hi] at h
  simpa only [carlemanSymmetric, carlemanSkew, LinearMap.add_apply, LinearMap.smul_apply,
    neg_sq, add_assoc, add_left_comm, add_comm] using h.symm


end

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def distanceSquare (x₀ : E) : SmoothScalar E :=
  ⟨fun x => ‖x-x₀‖^2, by
    change ContDiff ℝ ∞ (fun x : E => ‖x-x₀‖^2)
    exact (contDiff_id.sub (contDiff_const (c := x₀))).norm_sq ℝ⟩
@[simp] lemma distanceSquare_apply (x₀ x : E) : distanceSquare x₀ x = ‖x-x₀‖^2 := rfl

lemma distanceSquare_derivative_center (x₀ v : E) :
    SmoothScalar.directional v (distanceSquare x₀) x₀ = 0 := by
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) x₀).sub_const x₀).norm_sq
  simp only [id_eq] at hd
  change fderiv ℝ (fun x => ‖x-x₀‖^2) x₀ v = _
  rw [hd.fderiv]
  simp

def tangentPhase (ψ : SmoothScalar E) (x₀ : E) : SmoothScalar E := ψ - distanceSquare x₀
lemma tangentPhase_at (ψ : SmoothScalar E) (x₀ : E) (hψ : ψ x₀ = 0) : tangentPhase ψ x₀ x₀ = 0 := by
  simp [tangentPhase, hψ]
lemma tangentPhase_derivative_center (ψ : SmoothScalar E) (x₀ v : E) :
    SmoothScalar.directional v (tangentPhase ψ x₀) x₀ = SmoothScalar.directional v ψ x₀ := by
  change SmoothScalar.directional v (ψ - distanceSquare x₀) x₀ = _
  rw [map_sub]
  change SmoothScalar.directional v ψ x₀ - SmoothScalar.directional v (distanceSquare x₀) x₀ = _
  rw [distanceSquare_derivative_center, sub_zero]

lemma tangentPhase_annular_gap (ψ : SmoothScalar E) (x₀ x : E) (r H : ℝ)
    (hr : 0 < r) (hψ : ψ x ≤ 0) (hd : r/2 ≤ dist x x₀)
    (hsmall : -1 < H * tangentPhase ψ x₀ x) :
    convexifyPhase (tangentPhase ψ x₀) H x ≤ -r^2/8 := by
  have hnorm : r/2 ≤ ‖x-x₀‖ := by simpa only [dist_eq_norm] using hd
  have hs : r^2/4 ≤ ‖x-x₀‖^2 := by nlinarith [norm_nonneg (x-x₀)]
  have ht : tangentPhase ψ x₀ x ≤ -r^2/4 := by
    change ψ x - ‖x-x₀‖^2 ≤ _
    linarith
  have ht0 : tangentPhase ψ x₀ x ≤ 0 := ht.trans (by nlinarith [sq_nonneg r])
  have hmul := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1+H*tangentPhase ψ x₀ x) ht0
  change tangentPhase ψ x₀ x + (H/2)*(tangentPhase ψ x₀ x*tangentPhase ψ x₀ x) ≤ _
  nlinarith only [ht, hmul]



end YauCounterexamples
end

end OAI
