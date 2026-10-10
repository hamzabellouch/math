import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailAngularAlgebra
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailProductMean

namespace OAI

/-! Full-line Mellin transfer for the actual angular semiprime polynomial.
The complementary shifts are bounded by the true finite prime supports;
no Mellin frequency is discarded. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeAngularGaussPolynomial (ℓ : ℤ) (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  productGaussPolynomial (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j) ℓ u

def semiprimeAngularGaussSmoothed (ℓ : ℤ) (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  productGaussSmoothed (semiprimeFullSupport X i) (semiprimeFullSupport X j)
    (semiprimePartitionCoefficient X i) (semiprimePartitionCoefficient X j)
    ℓ primeProductEnvelope X u

lemma semiprimeAngularGaussPolynomial_bound (ℓ : ℤ) {X : ℝ} (hX : 0 < X)
    (i j : ℕ) (u : ℝ) :
    ‖semiprimeAngularGaussPolynomial ℓ X i j u‖ ≤
      1296*(semiprimePartitionScale i*semiprimePartitionScale j) := by
  have hb := semiprime_pair_norm_bound hX (by norm_num : (0:ℝ) ≤ 1) i j
    (fun p q => theta ℓ (p*q)*gauss (p*q)*normTwist u (p*q)) (by
      intro p hp q hq
      have hprimary := primary_mul (semiprimeFullSupport_bounds hX i hp).1
        (semiprimeFullSupport_bounds hX j hq).1
      simp only [norm_mul,norm_theta (primary_ne_zero hprimary) ℓ,norm_normTwist,
        one_mul,mul_one]
      exact norm_gauss_le_one hprimary)
  simpa only [semiprimeAngularGaussPolynomial,productGaussPolynomial,mul_one,mul_assoc] using hb

lemma semiprimeAngularGaussPolynomial_continuous (ℓ : ℤ) (X : ℝ) (i j : ℕ) :
    Continuous (semiprimeAngularGaussPolynomial ℓ X i j) :=
  productGaussPolynomial_continuous _ _ _ _ _

lemma semiprimeAngularGaussSmoothed_mellin (ℓ : ℤ) {X : ℝ} (hX : 0 < X)
    (i j : ℕ) (u : ℝ) :
    semiprimeAngularGaussSmoothed ℓ X i j u =
      ∫ τ : ℝ, zeroLineMellinWeight primeProductEnvelope X τ*
        semiprimeAngularGaussPolynomial ℓ X i j (u-τ) := by
  exact product_gauss_mellin _ _ _ _
    (fun p hp => (semiprimeFullSupport_bounds hX i hp).1)
    (fun p hp => (semiprimeFullSupport_bounds hX j hp).1)
    ℓ primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hX u

lemma semiprimeAngularGaussSmoothed_mellin_integrable (ℓ : ℤ) {X : ℝ} (hX : 0 < X)
    (i j : ℕ) (u : ℝ) :
    Integrable (fun τ : ℝ => zeroLineMellinWeight primeProductEnvelope X τ*
      semiprimeAngularGaussPolynomial ℓ X i j (u-τ)) :=
  product_gauss_mellin_integrable _ _ _ _ ℓ primeProductEnvelope
    primeProductEnvelope_compact primeProductEnvelope_positive primeProductEnvelope_smooth hX u

theorem semiprimeAngularGaussSmoothed_height_mean (ℓ : ℤ) {X E V U : ℝ}
    (hX : 0 < X) (i j : ℕ) (hE : 0 ≤ E) (hV : 0 < V) (hU : 0 < U) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖semiprimeAngularGaussPolynomial ℓ X i j (t+u)‖) U ≤ E) :
    dyadicHeightMean (fun t => ‖semiprimeAngularGaussSmoothed ℓ X i j t‖) U ≤
      E*zeroLineMellinMass primeProductEnvelope+
        (2592*(semiprimePartitionScale i*semiprimePartitionScale j))/V^n*
          zeroLineMellinMoment primeProductEnvelope n := by
  have hAi := semiprimePartitionScale_pos i
  have hBj := semiprimePartitionScale_pos j
  have hb := productGaussSmoothed_height_mean _ _ _ _
    (fun p hp => (semiprimeFullSupport_bounds hX i hp).1)
    (fun p hp => (semiprimeFullSupport_bounds hX j hp).1)
    ℓ primeProductEnvelope primeProductEnvelope_compact primeProductEnvelope_positive
    primeProductEnvelope_smooth hX
    (by positivity : 0 ≤ 1296*(semiprimePartitionScale i*semiprimePartitionScale j))
    hE hV hU (semiprimeAngularGaussPolynomial_bound ℓ hX i j) n hsmall
  exact hb.trans_eq (by congr 2; ring)

theorem semiprimeGaussTail_angular_window_transfer (ℓ : ℤ) {X E V H U : ℝ}
    (hX : 0 < X) (i j : ℕ) (hE : 0 ≤ E) (hV : 0 < V) (hH : 0 < H)
    (hU : 0 < U) (n : ℕ)
    (hsmall : ∀ u, |u| ≤ V →
      dyadicHeightMean (fun t => ‖semiprimeAngularGaussPolynomial ℓ X i j (t+u)‖) U ≤ E) :
    ‖semiprimeGaussTailPiece ℓ H U X i j‖ ≤
      2*(E*zeroLineMellinMass primeProductEnvelope+
        (2592*(semiprimePartitionScale i*semiprimePartitionScale j))/V^n*
          zeroLineMellinMoment primeProductEnvelope n) := by
  rw [semiprimeGaussTailPiece_window ℓ H U hX i j]
  exact (productGaussWindow_bound _ _ _ _ ℓ primeProductEnvelope hH hU X).trans
    (mul_le_mul_of_nonneg_left
      (semiprimeAngularGaussSmoothed_height_mean ℓ hX i j hE hV hU n hsmall)
      (by norm_num : (0:ℝ) ≤ 2))

end CubicFirstMoment

end

end OAI
