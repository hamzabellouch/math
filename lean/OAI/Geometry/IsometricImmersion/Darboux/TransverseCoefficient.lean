import OAI.Geometry.IsometricImmersion.Darboux.ActualDriftCoefficients
import OAI.Geometry.IsometricImmersion.Darboux.Drift
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

def flowRho (s : Coord → ℝ) : Coord → ℝ := coordPartial 1 s

def flowSigma (s : Coord → ℝ) : Coord → ℝ := coordPartial 1 (flowRho s)

def transverseA (g : MetricField) (z s : Coord → ℝ) (p : Coord) : ℝ :=
  gaussianCurvature g p * darbouxG g z p * (flowRho s p) ^ 2

def transversePartial (s f : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 f p / flowRho s p

def transverseC (g : MetricField) (z s : Coord → ℝ) (ell : ℕ) (p : Coord) : ℝ :=
  gaussianCurvature g p * darbouxG g z p * flowSigma s p + flowRho s p *
    (coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
      gaussianCurvature g p * curvatureDriftError g z p + (ell : ℝ) *
        (coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
          gaussianCurvature g p * coordPartial 1 (darbouxG g z) p))

def transverseRemainder (g : MetricField) (z s : Coord → ℝ)
    (ell : ℕ) (p : Coord) : ℝ :=
  (curvatureDriftError g z p - coordPartial 1 (darbouxG g z) p) /
      (darbouxG g z p * flowRho s p) -
    (2 * (ell : ℝ) + 1) * flowSigma s p / (flowRho s p) ^ 2

variable {g : MetricField} {z s : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem flowRho_contDiffOn (hU : IsOpen U) (hs : ContDiffOn ℝ ∞ s U) :
    ContDiffOn ℝ ∞ (flowRho s) U :=
  partial_contDiffOn hs hU 1

theorem flowSigma_contDiffOn (hU : IsOpen U) (hs : ContDiffOn ℝ ∞ s U) :
    ContDiffOn ℝ ∞ (flowSigma s) U :=
  partial_contDiffOn (flowRho_contDiffOn hU hs) hU 1

theorem transverseA_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hs : ContDiffOn ℝ ∞ s U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (transverseA g z s) U :=
  ((gaussianCurvature_contDiffOn hg hU).mul (darbouxG_contDiffOn hg hU hz hyy)).mul
    ((flowRho_contDiffOn hU hs).pow 2)

theorem transverseA_partial_y
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hs : ContDiffOn ℝ ∞ s U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U) :
    coordPartial 1 (transverseA g z s) p =
      (coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p * coordPartial 1 (darbouxG g z) p) * (flowRho s p) ^ 2 +
      2 * gaussianCurvature g p * darbouxG g z p * flowRho s p * flowSigma s p := by
  have hK : DifferentiableAt ℝ (gaussianCurvature g) p :=
    (((gaussianCurvature_contDiffOn hg hU) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (darbouxG g z) p :=
    (((darbouxG_contDiffOn hg hU hz hyy) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hrho : DifferentiableAt ℝ (flowRho s) p :=
    (((flowRho_contDiffOn hU hs) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by simp)
  have hd := (hK.hasFDerivAt.fun_mul hG.hasFDerivAt).fun_mul
    (hrho.hasFDerivAt.fun_mul hrho.hasFDerivAt)
  change coordPartial 1 (fun q => gaussianCurvature g q * darbouxG g z q *
    (flowRho s q) ^ 2) p = _
  simp only [coordPartial, flowSigma, pow_two]
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem transverseA_partial_s
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hs : ContDiffOn ℝ ∞ s U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    (hrho : 0 < flowRho s p) :
    transversePartial s (transverseA g z s) p =
      darbouxG g z p * flowRho s p * coordPartial 1 (gaussianCurvature g) p +
        gaussianCurvature g p * (flowRho s p * coordPartial 1 (darbouxG g z) p +
          2 * darbouxG g z p * flowSigma s p) := by
  rw [transversePartial, transverseA_partial_y hg hU hz hs hyy hp]
  field_simp [ne_of_gt hrho]
  ring

theorem transverseC_eq
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hs : ContDiffOn ℝ ∞ s U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    (hE : 0 < heightEnergy g z p) (hrho : 0 < flowRho s p) (ell : ℕ) :
    transverseC g z s ell p =
      ((ell : ℝ) + 1) * transversePartial s (transverseA g z s) p +
        transverseA g z s p * transverseRemainder g z s ell p := by
  have hG : darbouxG g z p ≠ 0 := ne_of_gt (darbouxG_pos g z p hE (hyy p hp))
  have hpoly := SmoothLocal.DriftAlgebra.transverse_coefficient_polynomial
    (ell : ℝ) (gaussianCurvature g p) (coordPartial 1 (gaussianCurvature g) p)
    (darbouxG g z p) (coordPartial 1 (darbouxG g z) p)
    (flowRho s p) (flowSigma s p) (curvatureDriftError g z p)
  have hfactor := SmoothLocal.DriftAlgebra.transverse_coefficient_factor
    (ell : ℝ) (gaussianCurvature g p) (darbouxG g z p)
    (coordPartial 1 (darbouxG g z) p) (flowRho s p) (flowSigma s p)
    (curvatureDriftError g z p) hG (ne_of_gt hrho)
  rw [transverseA_partial_s hg hU hz hs hyy hp hrho]
  dsimp only [transverseC, transverseA, transverseRemainder]
  rw [hpoly, hfactor]

theorem transversePartialA_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hs : ContDiffOn ℝ ∞ s U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hrho : ∀ p ∈ U, 0 < flowRho s p) :
    ContDiffOn ℝ ∞ (transversePartial s (transverseA g z s)) U :=
  (partial_contDiffOn (transverseA_contDiffOn hg hU hz hs hyy) hU 1).div
    (flowRho_contDiffOn hU hs) (fun p hp => ne_of_gt (hrho p hp))

theorem transverseRemainder_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hs : ContDiffOn ℝ ∞ s U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hrho : ∀ p ∈ U, 0 < flowRho s p) (ell : ℕ) :
    ContDiffOn ℝ ∞ (transverseRemainder g z s ell) U := by
  have hG := darbouxG_contDiffOn hg hU hz hyy
  have hGy := partial_contDiffOn hG hU 1
  have hR := curvatureDriftError_contDiffOn hg hU hz hyy
  have hρ := flowRho_contDiffOn hU hs
  have hσ := flowSigma_contDiffOn hU hs
  have hGrho : ∀ p ∈ U, darbouxG g z p * flowRho s p ≠ 0 := by
    intro p hp
    exact mul_ne_zero (ne_of_gt (darbouxG_pos g z p (hE p hp) (hyy p hp)))
      (ne_of_gt (hrho p hp))
  exact ((hR.sub hGy).div (hG.mul hρ) hGrho).sub
    ((contDiffOn_const.mul hσ).div (hρ.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (hrho p hp))))

theorem transverseRemainder_bounded_on_compact
    {Q : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hs : ContDiffOn ℝ ∞ s U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hrho : ∀ p ∈ U, 0 < flowRho s p) (ell : ℕ)
    (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Q, |transverseRemainder g z s ell p| ≤ B := by
  have hcont : ContinuousOn (transverseRemainder g z s ell) Q :=
    (transverseRemainder_contDiffOn hg hU hz hs hyy hE hrho ell).continuousOn.mono hQU
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro p hp
  have hb : |transverseRemainder g z s ell p| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB p hp
  exact hb.trans (le_max_left _ _)

theorem transverseRemainder_bound
    (g : MetricField) (z s : Coord → ℝ) (p : Coord) (ell : ℕ)
    (cG crho BR BGy Bsigma : ℝ)
    (hcG : 0 < cG) (hcrho : 0 < crho)
    (hG : cG ≤ darbouxG g z p) (hrho : crho ≤ flowRho s p)
    (hR : |curvatureDriftError g z p| ≤ BR)
    (hGy : |coordPartial 1 (darbouxG g z) p| ≤ BGy)
    (hsigma : |flowSigma s p| ≤ Bsigma) :
    |transverseRemainder g z s ell p| ≤
      (BR + BGy) / (cG * crho) + (2 * (ell : ℝ) + 1) * Bsigma / crho ^ 2 := by
  have hGpos : 0 < darbouxG g z p := hcG.trans_le hG
  have hrhopos : 0 < flowRho s p := hcrho.trans_le hrho
  have hBR : 0 ≤ BR := (abs_nonneg _).trans hR
  have hBGy : 0 ≤ BGy := (abs_nonneg _).trans hGy
  have hBσ : 0 ≤ Bsigma := (abs_nonneg _).trans hsigma
  have hell : 0 ≤ 2 * (ell : ℝ) + 1 :=
    add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg ell)) (by norm_num)
  have htri (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b
  have hnum : |curvatureDriftError g z p - coordPartial 1 (darbouxG g z) p| ≤ BR + BGy :=
    (htri _ _).trans (add_le_add hR hGy)
  have hden : cG * crho ≤ |darbouxG g z p * flowRho s p| := by
    rw [abs_of_pos (mul_pos hGpos hrhopos)]
    exact mul_le_mul hG hrho hcrho.le hGpos.le
  have hfirst :
      |(curvatureDriftError g z p - coordPartial 1 (darbouxG g z) p) /
        (darbouxG g z p * flowRho s p)| ≤ (BR + BGy) / (cG * crho) := by
    rw [abs_div]
    exact div_le_div₀ (add_nonneg hBR hBGy) hnum (mul_pos hcG hcrho) hden
  have hsecond : |(2 * (ell : ℝ) + 1) * flowSigma s p / (flowRho s p) ^ 2| ≤
      (2 * (ell : ℝ) + 1) * Bsigma / crho ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hell, abs_pow, abs_of_pos hrhopos]
    exact div_le_div₀ (mul_nonneg hell hBσ)
      (mul_le_mul_of_nonneg_left hsigma hell) (sq_pos_of_pos hcrho)
      (pow_le_pow_left₀ hcrho.le hrho 2)
  exact (htri _ _).trans (add_le_add hfirst hsecond)

end SmoothLocal.Geometry

end

end OAI
