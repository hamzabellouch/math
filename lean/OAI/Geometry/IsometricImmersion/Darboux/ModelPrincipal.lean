import OAI.Geometry.IsometricImmersion.Metrics.ModelCoercivity

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Model
open SmoothLocal.Geometry SmoothLocal.Weighted

def modelPrincipalRemainderBound (ell : ℕ) (R MG : ℝ) : ℝ :=
  ((ell : ℝ) + 1 / 2 + R / 2) * MG

def modelPrincipalRadius (g0 kappa rhoMax epsilon R MG : ℝ) (ell : ℕ) : ℝ :=
  min (kappa / 8) (modelCoercivityMargin g0 kappa rhoMax epsilon ell /
    (2 * (modelPrincipalRemainderBound ell R MG + 1)))

theorem modelPrincipalRemainderBound_nonneg (ell : ℕ) {R MG : ℝ}
    (hR : 0 ≤ R) (hMG : 0 ≤ MG) : 0 ≤ modelPrincipalRemainderBound ell R MG := by
  unfold modelPrincipalRemainderBound
  positivity

theorem modelPrincipalRadius_pos (ell : ℕ) {g0 kappa rhoMax epsilon R MG : ℝ}
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon)
    (hR : 0 ≤ R) (hMG : 0 ≤ MG) :
    0 < modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell := by
  have hmu := modelCoercivityMargin_pos ell hg0 hkappa hrho heps
  have hM := modelPrincipalRemainderBound_nonneg ell hR hMG
  unfold modelPrincipalRadius
  positivity

theorem modelPrincipal_derivative_remainder_bound
    {G : Coord → ℝ} {p : Coord} (ell : ℕ) {epsilon R MG : ℝ}
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ R)
    (hGs : |coordPartial 1 G p| ≤ MG) (hGt : |coordPartial 0 G p| ≤ MG) :
    |-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
      epsilon * p 0 * coordPartial 0 G p / 2| ≤ modelPrincipalRemainderBound ell R MG := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMG : 0 ≤ MG := (abs_nonneg _).trans hGs
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfirst : |-((ell : ℝ) + 1 / 2) * coordPartial 1 G p| ≤
      ((ell : ℝ) + 1 / 2) * MG := by
    rw [abs_mul, abs_neg, abs_of_nonneg hbeta]
    exact mul_le_mul_of_nonneg_left hGs hbeta
  have hprod : |epsilon * p 0 * coordPartial 0 G p| ≤ R * MG := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    have het : epsilon * |p 0| ≤ R :=
      (mul_le_mul_of_nonneg_left ht heps).trans (by nlinarith)
    exact mul_le_mul het hGt (abs_nonneg _) hR
  have hsecond : |epsilon * p 0 * coordPartial 0 G p / 2| ≤ R * MG / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right hprod (by norm_num)
  have hsum := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  unfold modelPrincipalRemainderBound
  nlinarith only [hsum]

theorem modelPrincipal_radius_error
    {g0 kappa rhoMax epsilon R MG K : ℝ} (ell : ℕ)
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon)
    (hR : 0 ≤ R) (hMG : 0 ≤ MG)
    (hK : |K| ≤ modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell) :
    |K| * modelPrincipalRemainderBound ell R MG ≤
      modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 := by
  let mu := modelCoercivityMargin g0 kappa rhoMax epsilon ell
  let M := modelPrincipalRemainderBound ell R MG
  have hmu : 0 < mu := modelCoercivityMargin_pos ell hg0 hkappa hrho heps
  have hM : 0 ≤ M := modelPrincipalRemainderBound_nonneg ell hR hMG
  have hden : 0 < 2 * (M + 1) := by positivity
  have hK' : |K| ≤ mu / (2 * (M + 1)) := hK.trans (min_le_right _ _)
  calc
    _ ≤ mu / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hK' hM
    _ ≤ mu / (2 * (M + 1)) * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_pos hmu hden).le
    _ = mu / 2 := by field_simp [show M + 1 ≠ 0 by positivity]

theorem model_full_principal_lower
    {G K : Coord → ℝ} {p : Coord} {y kappa g0 rho rhoMax epsilon R MG Mq q : ℝ}
    (ell : ℕ) (hGdiff : DifferentiableAt ℝ G p) (hKdiff : DifferentiableAt ℝ K p)
    (hkappa : 0 < kappa) (hg0 : 0 < g0) (hG : g0 ≤ G p)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (ht : |p 0| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hy : y ≤ 1 / 50)
    (hGsi : |coordPartial 1 G p| ≤ MG) (hGti : |coordPartial 0 G p| ≤ MG)
    (hKvalue : K p = modelCurvature kappa ![p 0, y])
    (hKs : coordPartial 1 K p = coordPartial 1 (modelCurvature kappa) ![p 0, y] / rho)
    (hKt : coordPartial 0 K p = 2 * kappa * p 0 -
      q * coordPartial 1 (modelCurvature kappa) ![p 0, y])
    (hKsmall : |K p| ≤ modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (fun z => G z * K z) ell epsilon p := by
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMG : 0 ≤ MG := (abs_nonneg _).trans hGsi
  have hmodel : |modelCurvature kappa ![p 0, y]| ≤ kappa / 8 := by
    rw [← hKvalue]
    exact hKsmall.trans (min_le_left _ _)
  have hgeo := model_geometric_principal_lower (p := ![p 0, y]) ell hkappa hg0 hG
    hrho hrhoMax heps (by simpa using ht) hq hsmall (by simpa using hy) hmodel
  simp only [Matrix.cons_val_zero] at hgeo
  have hcoeff := modelPrincipal_derivative_remainder_bound ell heps.le heps1 ht hGsi hGti
  have herr : |K p * (-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
      epsilon * p 0 * coordPartial 0 G p / 2)| ≤
      modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)).trans
      (modelPrincipal_radius_error ell hg0 hkappa hmax heps hR hMG hKsmall)
  have heq : directedPrincipal (fun z => G z * K z) ell epsilon p =
      G p * (-(((ell : ℝ) + 1 / 2) / rho + epsilon * p 0 * q / 2) *
        coordPartial 1 (modelCurvature kappa) ![p 0, y] + epsilon * kappa * (p 0) ^ 2) +
      K p * (-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
        epsilon * p 0 * coordPartial 0 G p / 2) := by
    unfold directedPrincipal
    rw [HessianCalculus.coordPartial_mul_at hGdiff hKdiff 1,
      HessianCalculus.coordPartial_mul_at hGdiff hKdiff 0, hKs, hKt]
    field_simp [hrho.ne']
    ring
  rw [heq]
  linarith [(abs_le.mp herr).1]

end SmoothLocal.Model

end

end OAI
