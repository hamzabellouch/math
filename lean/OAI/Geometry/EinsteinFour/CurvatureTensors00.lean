import OAI.Geometry.EinsteinFour.BianchiHessian
import OAI.Geometry.EinsteinFour.WeylEstimates00

namespace OAI


section

/-!
# The axial reduction of the quadratic coupling terms

The exact matrix certificate (21) implies the full three-variable quadratic
inequality. The proof multiplies by the positive `P0 * v` and applies the
closed two-by-two determinant criterion, so it also covers the axial endpoint.
-/

namespace PositiveEinsteinFour

open Quadratic Potential

noncomputable section

/-- The spectral Schur completion, including `σ = 1`. -/
theorem spectral_schur_nonneg
    (v P σ ρ D W p : ℝ)
    (hv : 0 < v) (hP : 0 < P)
    (hσlower : -1 ≤ σ) (hσupper : σ ≤ 1)
    (hcircle : ρ ^ 2 = 1 - σ ^ 2)
    (hA : 0 ≤ P * v * D - (1 + σ) * v ^ 2 * W ^ 2) :
    0 ≤ (1 - σ) * v * P / 3 * p ^ 2 -
      2 * v * ρ / Real.sqrt 3 * p * W + D := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hdet : (-P * ρ / Real.sqrt 3) ^ 2 =
      ((1 - σ) * P ^ 2 / 3) * (1 + σ) := by
    rw [div_pow, hsqrt]
    calc
      (-P * ρ) ^ 2 / 3 = P ^ 2 * ρ ^ 2 / 3 := by ring
      _ = ((1 - σ) * P ^ 2 / 3) * (1 + σ) := by rw [hcircle]; ring
  have hσgap : 0 ≤ 1 - σ := by linarith
  have hsmall := quadratic_form_nonneg_of_det
    ((1 - σ) * P ^ 2 / 3) (1 + σ) (-P * ρ / Real.sqrt 3)
    (by positivity) (by linarith) (le_of_eq hdet) p W
  have hscaled : 0 ≤ v ^ 2 *
      (((1 - σ) * P ^ 2 / 3) * p ^ 2 +
        2 * (-P * ρ / Real.sqrt 3) * p * W + (1 + σ) * W ^ 2) :=
    mul_nonneg (sq_nonneg v) hsmall
  have hidentity :
      P * v * ((1 - σ) * v * P / 3 * p ^ 2 -
        2 * v * ρ / Real.sqrt 3 * p * W + D) =
      (P * v * D - (1 + σ) * v ^ 2 * W ^ 2) +
        v ^ 2 * (((1 - σ) * P ^ 2 / 3) * p ^ 2 +
          2 * (-P * ρ / Real.sqrt 3) * p * W + (1 + σ) * W ^ 2) := by ring
  have hproduct : 0 ≤ P * v * ((1 - σ) * v * P / 3 * p ^ 2 -
      2 * v * ρ / Real.sqrt 3 * p * W + D) := by
    rw [hidentity]
    exact add_nonneg hA hscaled
  exact nonneg_of_mul_nonneg_right hproduct (mul_pos hP hv)

/-- The pure non-axial block in the quadratic part of the plus Weyl estimate. -/
def lowerBlock (v b σ k l : ℝ) : ℝ :=
  (K1 v b σ - 5 * kappa v b / v) * k ^ 2 +
    2 * K12 v b σ * k * l + (K2 v b σ - kappa v b / v) * l ^ 2

/-- Polynomial-matrix form (21) is the numerator of the Schur complement. -/
theorem spectral_matrix_as_schur (v b σ k l : ℝ) (hv : v ≠ 0) :
    A11 v b σ * k ^ 2 + 2 * A12 v b σ * k * l + A22 v b σ * l ^ 2 =
      P0 v b * v * lowerBlock v b σ k l -
        (1 + σ) * v ^ 2 * (Pk v b * k + Pl v b * l) ^ 2 := by
  unfold A11 A12 A22 lowerBlock
  field_simp [hv]
  ring

/-- The loss from moving off the axial spectral shape is nonnegative, for all
first-derivative variables. This is the quadratic axial reduction in Section 6.
The closed domain and `σ = 1` are included. -/
theorem axial_reduction_nonneg
    {v b σ ρ : ℝ} (hv : 0 < v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (hσlower : -1 ≤ σ) (hσupper : σ ≤ 1) (hcircle : ρ ^ 2 = 1 - σ ^ 2)
    (p k l : ℝ) :
    0 ≤ (1 - σ) * v * P0 v b / 3 * p ^ 2 -
      2 * v * ρ / Real.sqrt 3 * p * (Pk v b * k + Pl v b * l) +
        lowerBlock v b σ k l := by
  have hd : 0 ≤ 2 - v - b := by linarith
  have hw : 0 ≤ weight v b := sq_nonneg _
  have hP : 0 < P0 v b := by
    unfold P0 Pk
    positivity
  apply spectral_schur_nonneg v (P0 v b) σ ρ (lowerBlock v b σ k l)
    (Pk v b * k + Pl v b * l) p hv hP hσlower hσupper hcircle
  rw [← spectral_matrix_as_schur v b σ k l (ne_of_gt hv)]
  exact spectral_matrix_nonneg hv.le hb hsum hσupper k l

end
end PositiveEinsteinFour
end


section

/-! The quadratic axial comparison on the actual four-vector parameters. -/

namespace PositiveEinsteinFour.Bianchi

open scoped BigOperators
open Quadratic Potential

noncomputable section

def axialLoss (v b σ ρ : ℝ) (p k l : Vec) : ℝ :=
  (1 - σ) * v * P0 v b / 3 * ‖p‖ ^ 2 +
    2 * v * ρ / Real.sqrt 3 *
      (Pk v b * inner ℝ p k + Pl v b * inner ℝ p l) +
    (K1 v b σ - 5 * kappa v b / v) * ‖k‖ ^ 2 +
    2 * K12 v b σ * inner ℝ k l +
    (K2 v b σ - kappa v b / v) * ‖l‖ ^ 2

/-- Sum the scalar Schur certificate over the actual tangent coordinates.
All inner products retain their signs. -/
theorem axialLoss_nonneg {v b σ ρ : ℝ}
    (hv : 0 < v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (hσlower : -1 ≤ σ) (hσupper : σ ≤ 1)
    (hcircle : ρ ^ 2 = 1 - σ ^ 2) (p k l : Vec) :
    0 ≤ axialLoss v b σ ρ p k l := by
  have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    axial_reduction_nonneg hv hb hsum hσlower hσupper hcircle (-p i) (k i) (l i))
  have hid : (∑ i : Fin 4,
      ((1 - σ) * v * P0 v b / 3 * (-p i) ^ 2 -
        2 * v * ρ / Real.sqrt 3 * (-p i) * (Pk v b * k i + Pl v b * l i) +
          lowerBlock v b σ (k i) (l i))) = axialLoss v b σ ρ p k l := by
    simp only [axialLoss, lowerBlock, EuclideanSpace.real_norm_sq_eq,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simp only [Fin.sum_univ_succ]
    ring
  rwa [hid] at h

/-- The plus part of the genuine quadratic integrand before the scalar
derivatives of `κ` and the variance correction are added. -/
def blockQuadratic (S : Shape) (v b τ : ℝ) (p k l : Vec) : ℝ :=
  weight v b * hessianTensorForm S v b p k l +
    (17 / 10 : ℝ) *
      (6 * (S.sigma * v ^ 2 + τ * b ^ 2 - v - b) - 26 * (2 - v - b)) *
      ((parameters S p k l).squaredNorm / 6) +
    68 * (2 - v - b) * curvatureContraction S v (parameters S p k l) +
    kappa v b * (((parameters S p k l).squaredNorm / 6 - ‖p‖ ^ 2) / v)

/-- Exact collection of the gap from the axial value. The only additional
term is the nonnegative loss from the opposite block's nonaxial spectrum. -/
theorem blockQuadratic_gap (S : Shape) (v b τ : ℝ) (hv : v ≠ 0) (p k l : Vec) :
    (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 -
        blockQuadratic S v b τ p k l =
      axialLoss v b S.sigma S.rho p k l +
        (51 / 5 : ℝ) * (1 - τ) * b ^ 2 *
          ((parameters S p k l).squaredNorm / 6) := by
  rw [blockQuadratic, hessianTensor_matrix, curvatureContraction_parameters,
    parameters_energy]
  unfold axialLoss axialCoefficient P0 Pk Pl K1 K2 K12
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hv, hsqrt0]
  ring_nf
  rw [hsqrt]
  ring

/-- Equation (21) bounds the complete plus quadratic contribution by its
axial value, including the true Bianchi energy and all tangent pairings. -/
theorem blockQuadratic_le_axial (S : Shape) {v b τ : ℝ}
    (hv : 0 < v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (hτ : τ ≤ 1)
    (p k l : Vec) :
    blockQuadratic S v b τ p k l ≤
      (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 := by
  have hlo : -1 ≤ S.sigma := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  have hhi : S.sigma ≤ 1 := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  have hA := axialLoss_nonneg hv hb hsum hlo hhi S.sigma_rho_circle p k l
  have he : 0 ≤ (parameters S p k l).squaredNorm / 6 := by
    rw [parameters_energy]
    positivity
  have hτgap : 0 ≤ 1 - τ := by linarith
  have hother : 0 ≤ (51 / 5 : ℝ) * (1 - τ) * b ^ 2 *
      ((parameters S p k l).squaredNorm / 6) := by positivity
  have hgap := blockQuadratic_gap S v b τ (ne_of_gt hv) p k l
  linarith

end
end PositiveEinsteinFour.Bianchi
end


section

/-! The scalar axial completion is applied coordinatewise to the actual
four-dimensional tangent vectors, retaining all mixed inner products. -/

namespace PositiveEinsteinFour

open scoped BigOperators
open Quadratic Potential Bianchi

noncomputable section

/-- Equation (21) controls the complete tangent-vector quadratic form. -/
theorem axial_reduction_vectors
    {v b σ ρ : ℝ} (hv : 0 < v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (hσlower : -1 ≤ σ) (hσupper : σ ≤ 1) (hcircle : ρ ^ 2 = 1 - σ ^ 2)
    (p k l : Vec) :
    0 ≤ (1 - σ) * v * P0 v b / 3 * ‖p‖ ^ 2 -
      2 * v * ρ / Real.sqrt 3 *
        (Pk v b * inner ℝ p k + Pl v b * inner ℝ p l) +
      (K1 v b σ - 5 * kappa v b / v) * ‖k‖ ^ 2 +
      2 * K12 v b σ * inner ℝ k l +
      (K2 v b σ - kappa v b / v) * ‖l‖ ^ 2 := by
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    axial_reduction_nonneg hv hb hsum hσlower hσupper hcircle (p i) (k i) (l i))
  have hs (i : Fin 4) :
      (1 - σ) * v * P0 v b / 3 * (p i) ^ 2 -
        2 * v * ρ / Real.sqrt 3 * p i * (Pk v b * k i + Pl v b * l i) +
        lowerBlock v b σ (k i) (l i) =
      (1 - σ) * v * P0 v b / 3 * (p i) ^ 2 -
        2 * v * ρ / Real.sqrt 3 *
          (Pk v b * (k i * p i) + Pl v b * (l i * p i)) +
        (K1 v b σ - 5 * kappa v b / v) * (k i) ^ 2 +
        2 * K12 v b σ * (l i * k i) +
        (K2 v b σ - kappa v b / v) * (l i) ^ 2 := by
    unfold lowerBlock
    ring
  simp_rw [hs] at hn
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_add, mul_assoc] using hn

/-- The complete plus-block quadratic contribution before axial reduction.
The opposite cubic invariant is kept as `τ`. -/
def hessianQuadraticContribution (S : Shape) (v b τ : ℝ) (p k l : Vec) : ℝ :=
  weight v b * hessianTensorForm S v b p k l +
    (17 / 10 : ℝ) *
      ((6 * (S.sigma * v ^ 2 + τ * b ^ 2 - v - b) - 26 * (2 - v - b)) *
          ((parameters S p k l).squaredNorm / 6) +
        40 * (2 - v - b) * curvatureContraction S v (parameters S p k l)) +
    kappa v b * (((parameters S p k l).squaredNorm / 6 - ‖p‖ ^ 2) / v)

private theorem hessian_quadratic_axial_identity (S : Shape) (v b τ : ℝ)
    (p k l : Vec) (hv : v ≠ 0) :
    (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 -
        hessianQuadraticContribution S v b τ p k l =
      ((1 - S.sigma) * v * P0 v b / 3 * ‖p‖ ^ 2 +
        2 * v * S.rho / Real.sqrt 3 *
          (Pk v b * inner ℝ p k + Pl v b * inner ℝ p l) +
        (K1 v b S.sigma - 5 * kappa v b / v) * ‖k‖ ^ 2 +
        2 * K12 v b S.sigma * inner ℝ k l +
        (K2 v b S.sigma - kappa v b / v) * ‖l‖ ^ 2) +
      (51 / 5 : ℝ) * (1 - τ) * b ^ 2 * ((parameters S p k l).squaredNorm / 6) := by
  unfold hessianQuadraticContribution
  rw [hessianTensor_matrix, parameters_energy, curvatureContraction_parameters]
  unfold axialCoefficient P0 Pk Pl K1 K2 K12
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsq : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hv, hsq]
  ring_nf
  rw [hsqrt]
  ring

/-- The full quadratic contribution is bounded by its axial value, with
all three derivative variables still actual tangent vectors. -/
theorem hessian_quadratic_axial_bound (S : Shape) {v b τ : ℝ}
    (hv : 0 < v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (hτ : τ ≤ 1)
    (p k l : Vec) :
    hessianQuadraticContribution S v b τ p k l ≤
      (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 := by
  have hσlo : -1 ≤ S.sigma := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  have hσhi : S.sigma ≤ 1 := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  have ha := axial_reduction_vectors hv hb hsum hσlo hσhi
    (by nlinarith [S.sigma_rho_circle]) (-p) k l
  simp only [norm_neg, inner_neg_left] at ha
  have hE : 0 ≤ (parameters S p k l).squaredNorm / 6 := by
    rw [parameters_energy]
    positivity
  have ht : 0 ≤ (51 / 5 : ℝ) * (1 - τ) * b ^ 2 *
      ((parameters S p k l).squaredNorm / 6) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hτ)
      · exact sq_nonneg b
    · exact hE
  have hi := hessian_quadratic_axial_identity S v b τ p k l (ne_of_gt hv)
  linarith only [ha, ht, hi]

end
end PositiveEinsteinFour
end


section

/-! The actual quadratic terms reduce to the certified scalar matrix. -/

namespace PositiveEinsteinFour.Bianchi

open Quadratic Potential

noncomputable section

/-- Both block contributions, the differentiated scalar multipliers, and
the derivative term of the variance correction. -/
def coupledQuadratic (S T : Shape) (v b : ℝ) (p k l q kb lb : Vec) : ℝ :=
  blockQuadratic S v b T.sigma p k l + blockQuadratic T b v S.sigma q kb lb +
    kappaV v b * ‖p‖ ^ 2 + kappaB v b * inner ℝ p q +
    kappaV b v * ‖q‖ ^ 2 + kappaB b v * inner ℝ q p +
    158 * ‖p - q‖ ^ 2 / denominator v b

theorem coupledQuadratic_le_matrix (S T : Shape) {v b : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2) (p k l q kb lb : Vec) :
    coupledQuadratic S T v b p k l q kb lb ≤
      quadraticCoefficient v b * ‖p‖ ^ 2 +
        2 * mixedCoefficient v b * inner ℝ p q +
        quadraticCoefficient b v * ‖q‖ ^ 2 := by
  have hσ : S.sigma ≤ 1 := by nlinarith [S.sigma_rho_circle, sq_nonneg S.rho]
  have hτ : T.sigma ≤ 1 := by nlinarith [T.sigma_rho_circle, sq_nonneg T.rho]
  have hplus := blockQuadratic_le_axial S hv hb.le hsum hτ p k l
  have hminus := blockQuadratic_le_axial T hb hv.le (by linarith) hσ q kb lb
  have hid :
      (axialCoefficient v b + 2 * kappa v b / (3 * v)) * ‖p‖ ^ 2 +
        (axialCoefficient b v + 2 * kappa b v / (3 * b)) * ‖q‖ ^ 2 +
        kappaV v b * ‖p‖ ^ 2 + kappaB v b * inner ℝ p q +
        kappaV b v * ‖q‖ ^ 2 + kappaB b v * inner ℝ q p +
        158 * ‖p - q‖ ^ 2 / denominator v b =
      quadraticCoefficient v b * ‖p‖ ^ 2 +
        2 * mixedCoefficient v b * inner ℝ p q +
        quadraticCoefficient b v * ‖q‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm q p]
    unfold quadraticCoefficient mixedCoefficient
    have hd : denominator b v = denominator v b := by unfold denominator; ring
    rw [hd]
    ring
  rw [← hid]
  unfold coupledQuadratic
  linarith

/-- The full quadratic piece of the coupled integrand satisfies the target
bound, with the original fixed block labels and tangent pairing. -/
theorem coupledQuadratic_bound (S T : Shape) {v b : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hsum : v + b ≤ 2) (p k l q kb lb : Vec) :
    coupledQuadratic S T v b p k l q kb lb ≤
      2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2) := by
  exact (coupledQuadratic_le_matrix S T hv hb hsum p k l q kb lb).trans
    (hilbert_quadratic_bound_closed hv.le hb.le hsum p q
      (by intro h; exact (ne_of_gt hv h).elim)
      (by intro h; exact (ne_of_gt hb h).elim))

end
end PositiveEinsteinFour.Bianchi
end

end OAI
