import OAI.Geometry.IsometricImmersion.Metrics.ModelProfile
import OAI.Geometry.IsometricImmersion.Energy.DirectedCoercivity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model

open SmoothLocal.Geometry SmoothLocal.Weighted

theorem squareTransition_deriv_zero_left {t : ℝ} (ht : t ≤ 1 / 4) :
    deriv squareTransition t = 0 := by
  have hmin : IsLocalMin squareTransition t := Filter.Eventually.of_forall (fun x => by
    rw [squareTransition_zero ht]
    exact (squareTransition_range x).1)
  exact hmin.deriv_eq_zero

theorem squareTransition_deriv_zero_right {t : ℝ} (ht : 1 / 2 ≤ t) :
    deriv squareTransition t = 0 := by
  have hmax : IsLocalMax squareTransition t := Filter.Eventually.of_forall (fun x => by
    rw [squareTransition_one ht]
    exact (squareTransition_range x).2)
  exact hmax.deriv_eq_zero

theorem modelProfile_deriv_outer {y : ℝ} (hy : 1 / 2 ≤ y ^ 2) :
    deriv modelProfile y = -2 * y := by
  rw [modelProfile_deriv, squareTransition_one hy, squareTransition_deriv_zero_right hy]
  ring

theorem modelProfile_deriv_nonneg_lower_cap {y : ℝ} (hy : y ≤ 1 / 50) :
    0 ≤ deriv modelProfile y := by
  by_cases hy0 : y ≤ 0
  · rw [modelProfile_deriv]
    have hy3 : y ^ 3 ≤ 0 := by
      have hh := mul_nonpos_of_nonpos_of_nonneg hy0 (sq_nonneg y)
      nlinarith only [hh]
    have hfirst : 0 ≤ -2 * y * squareTransition (y ^ 2) :=
      mul_nonneg (by linarith) (squareTransition_range _).1
    have hsecond : 0 ≤ -2 * y ^ 3 * deriv squareTransition (y ^ 2) :=
      mul_nonneg (by linarith) (squareTransition_deriv_nonneg _)
    linarith
  · have hypos : 0 < y := lt_of_not_ge hy0
    have hysq : y ^ 2 ≤ 1 / 4 :=
      (pow_le_pow_left₀ hypos.le hy 2).trans (by norm_num)
    rw [modelProfile_deriv, squareTransition_zero hysq, squareTransition_deriv_zero_left hysq]
    norm_num

theorem modelProfile_deriv_lower_three_quarters {y : ℝ} (hy : y ≤ -(3 / 4 : ℝ)) :
    3 / 2 ≤ deriv modelProfile y := by
  have hs : (3 / 4 : ℝ) ^ 2 ≤ (-y) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith : (3 / 4 : ℝ) ≤ -y) 2
  have hysq : 1 / 2 ≤ y ^ 2 := by nlinarith only [hs]
  rw [modelProfile_deriv_outer hysq]
  linarith

theorem modelProfile_middle_lower {y : ℝ}
    (hylo : -(3 / 4 : ℝ) ≤ y) (hyhi : y ≤ 1 / 50) :
    7 / 16 ≤ modelProfile y := by
  have hy2 : y ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := sq_le_sq' hylo (by linarith)
  nlinarith [(modelProfile_bounds y).1]

theorem modelCurvature_partial (kappa : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (modelCurvature kappa) p =
      if i = 0 then 2 * kappa * p 0 else -kappa * deriv modelProfile (p 1) := by
  have hx := hasFDerivAt_apply (𝕜 := ℝ) 0 p
  have hy := ((modelProfile_contDiff.differentiable (by simp) (p 1)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hd := ((hx.pow 2).sub hy).const_mul kappa
  simp only [Function.comp_def, Pi.sub_def] at hd
  change fderiv ℝ (fun q : Coord => kappa * ((q 0) ^ 2 - modelProfile (q 1))) p
    (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp
  ring

theorem modelCurvature_partial_y_nonpos {kappa : ℝ} (hkappa : 0 ≤ kappa)
    {p : Coord} (hy : p 1 ≤ 1 / 50) : coordPartial 1 (modelCurvature kappa) p ≤ 0 := by
  rw [modelCurvature_partial]
  norm_num only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkappa)
    (modelProfile_deriv_nonneg_lower_cap hy)

theorem modelCurvature_negative_y_slope {kappa : ℝ} (hkappa : 0 ≤ kappa)
    {p : Coord} (hy : p 1 ≤ -(3 / 4 : ℝ)) :
    3 * kappa / 2 ≤ -coordPartial 1 (modelCurvature kappa) p := by
  rw [modelCurvature_partial]
  rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  have hm := mul_le_mul_of_nonneg_left (modelProfile_deriv_lower_three_quarters hy) hkappa
  nlinarith only [hm]

theorem modelCurvature_middle_xsq_lower {kappa : ℝ} (hkappa : 0 < kappa)
    {p : Coord} (hylo : -(3 / 4 : ℝ) ≤ p 1) (hyhi : p 1 ≤ 1 / 50)
    (hK : |modelCurvature kappa p| ≤ kappa / 8) :
    5 / 16 ≤ (p 0) ^ 2 := by
  have hh := mul_le_mul_of_nonneg_left (modelProfile_middle_lower hylo hyhi) hkappa.le
  have hlower := (abs_le.mp hK).1
  unfold modelCurvature at hlower
  have hprod : kappa * (5 / 16) ≤ kappa * (p 0) ^ 2 := by nlinarith only [hh, hlower]
  exact le_of_mul_le_mul_left hprod hkappa

def modelCoercivityMargin (g0 kappa rhoMax epsilon : ℝ) (ell : ℕ) : ℝ :=
  g0 * kappa * min (3 * ((ell : ℝ) + 1 / 2) / (4 * rhoMax)) (5 * epsilon / 16)

theorem modelCoercivityMargin_pos {g0 kappa rhoMax epsilon : ℝ} (ell : ℕ)
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon) :
    0 < modelCoercivityMargin g0 kappa rhoMax epsilon ell := by
  have hell : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  unfold modelCoercivityMargin
  positivity

theorem directed_model_slope_lower {rho rhoMax epsilon R Mq t q : ℝ} (ell : ℕ)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 ≤ epsilon)
    (ht : |t| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax) :
    ((ell : ℝ) + 1 / 2) / (2 * rhoMax) ≤
      ((ell : ℝ) + 1 / 2) / rho + epsilon * t * q / 2 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMq : 0 ≤ Mq := (abs_nonneg _).trans hq
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hbeta : 0 ≤ (ell : ℝ) + 1 / 2 := by positivity
  have hfrac : ((ell : ℝ) + 1 / 2) / rhoMax ≤ ((ell : ℝ) + 1 / 2) / rho :=
    (div_le_div_iff₀ hmax hrho).2 (mul_le_mul_of_nonneg_left hrhoMax hbeta)
  have hprod : |epsilon * t * q| ≤ epsilon * R * Mq := by
    rw [abs_mul, abs_mul, abs_of_nonneg heps]
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht heps) hq
      (abs_nonneg _) (mul_nonneg heps hR)
  have hprodlo := (abs_le.mp (hprod.trans hsmall)).1
  have he : ((ell : ℝ) + 1 / 2) / (2 * rhoMax) =
      (((ell : ℝ) + 1 / 2) / rhoMax) / 2 := by ring
  rw [he]
  linarith

theorem model_geometric_principal_lower
    {kappa g0 G rho rhoMax epsilon R Mq q : ℝ} {p : Coord} (ell : ℕ)
    (hkappa : 0 < kappa) (hg0 : 0 < g0) (hG : g0 ≤ G)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 < epsilon)
    (ht : |p 0| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hy : p 1 ≤ 1 / 50) (hK : |modelCurvature kappa p| ≤ kappa / 8) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell ≤
      G * (-(((ell : ℝ) + 1 / 2) / rho + epsilon * p 0 * q / 2) *
        coordPartial 1 (modelCurvature kappa) p + epsilon * kappa * (p 0) ^ 2) := by
  let beta : ℝ := (ell : ℝ) + 1 / 2
  let coef : ℝ := beta / rho + epsilon * p 0 * q / 2
  let amin : ℝ := beta / (2 * rhoMax)
  let base : ℝ := coef * (-coordPartial 1 (modelCurvature kappa) p) + epsilon * kappa * (p 0) ^ 2
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hamin : 0 < amin := by dsimp [amin]; positivity
  have hcoef : amin ≤ coef := directed_model_slope_lower ell hrho hrhoMax heps.le ht hq hsmall
  have hKy : 0 ≤ -coordPartial 1 (modelCurvature kappa) p :=
    neg_nonneg.mpr (modelCurvature_partial_y_nonpos hkappa.le hy)
  have hterm : 0 ≤ epsilon * kappa * (p 0) ^ 2 := by positivity
  have hbase : 0 ≤ base := by dsimp [base]; exact add_nonneg (mul_nonneg (hamin.le.trans hcoef) hKy) hterm
  have hlower : kappa * min (3 * beta / (4 * rhoMax)) (5 * epsilon / 16) ≤ base := by
    by_cases hylo : p 1 ≤ -(3 / 4 : ℝ)
    · have hslope := modelCurvature_negative_y_slope hkappa.le hylo
      calc
        _ ≤ kappa * (3 * beta / (4 * rhoMax)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hkappa.le
        _ = amin * (3 * kappa / 2) := by dsimp [amin]; ring
        _ ≤ amin * (-coordPartial 1 (modelCurvature kappa) p) :=
          mul_le_mul_of_nonneg_left hslope hamin.le
        _ ≤ coef * (-coordPartial 1 (modelCurvature kappa) p) := mul_le_mul_of_nonneg_right hcoef hKy
        _ ≤ base := by dsimp [base]; linarith
    · have hxsq := modelCurvature_middle_xsq_lower hkappa (lt_of_not_ge hylo).le hy hK
      calc
        _ ≤ kappa * (5 * epsilon / 16) := mul_le_mul_of_nonneg_left (min_le_right _ _) hkappa.le
        _ = epsilon * kappa * (5 / 16) := by ring
        _ ≤ epsilon * kappa * (p 0) ^ 2 := mul_le_mul_of_nonneg_left hxsq (mul_pos heps hkappa).le
        _ ≤ base := by
          dsimp [base]
          have hn := mul_nonneg (hamin.le.trans hcoef) hKy
          linarith
  have hfirst := mul_le_mul_of_nonneg_left hlower hg0.le
  have hsecond := mul_le_mul_of_nonneg_right hG hbase
  unfold modelCoercivityMargin
  dsimp only [base, coef, beta] at hfirst hsecond
  nlinarith only [hfirst, hsecond]

end SmoothLocal.Model

end

end OAI
