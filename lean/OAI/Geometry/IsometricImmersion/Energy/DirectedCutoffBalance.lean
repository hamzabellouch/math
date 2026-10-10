import OAI.Geometry.IsometricImmersion.Energy.MultiplierIntegral
import OAI.Geometry.IsometricImmersion.Caps.EllipticAbsorption

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def multiplierCutoffError (A chi m n u : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 chi p * multiplierFluxT A m n u p +
    coordPartial 1 chi p * multiplierFluxS A m n u p

theorem multiplier_divergence_quadratic
    {A B C m n u : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * multiplierTest m n u p =
      coordPartial 0 (multiplierFluxT A m n u) p + coordPartial 1 (multiplierFluxS A m n u) p +
        multiplierQuadratic A B C m n u p := by
  have hh := multiplier_divergence_identity (B := B) (C := C) hA hm hn hu hU hp
  unfold multiplierQuadratic
  linear_combination hh

theorem multiplierQuadratic_cutoff_split
    {A B C chi m n u : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hm : ContDiffOn ℝ ∞ m U) (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U)
    (hp : p ∈ U) :
    multiplierQuadratic A B C (fun q => chi q * m q) (fun q => chi q * n q) u p =
      chi p * multiplierQuadratic A B C m n u p - multiplierCutoffError A chi m n u p := by
  have hAd := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hmd := (hm.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hnd := (hn.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hcd := (hchi.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hbase := multiplier_divergence_quadratic (B := B) (C := C) hAd hmd hnd hu hU hp
  have hcut := multiplier_divergence_quadratic (B := B) (C := C) hAd (hcd.mul hmd) (hcd.mul hnd) hu hU hp
  change multiplierOperator A B C u p *
      multiplierTest (fun q => chi q * m q) (fun q => chi q * n q) u p =
    coordPartial 0 (multiplierFluxT A (fun q => chi q * m q) (fun q => chi q * n q) u) p +
      coordPartial 1 (multiplierFluxS A (fun q => chi q * m q) (fun q => chi q * n q) u) p +
      multiplierQuadratic A B C (fun q => chi q * m q) (fun q => chi q * n q) u p at hcut
  have htest : multiplierTest (fun q => chi q * m q) (fun q => chi q * n q) u p =
      chi p * multiplierTest m n u p := by unfold multiplierTest; ring
  have hFt : multiplierFluxT A (fun q => chi q * m q) (fun q => chi q * n q) u =
      (fun q => chi q * multiplierFluxT A m n u q) := by funext q; unfold multiplierFluxT; ring
  have hFs : multiplierFluxS A (fun q => chi q * m q) (fun q => chi q * n q) u =
      (fun q => chi q * multiplierFluxS A m n u q) := by funext q; unfold multiplierFluxS; ring
  obtain ⟨hFts, hFss⟩ := multiplierFluxes_contDiffOn hU hA hm hn hu
  rw [htest, hFt, hFs,
    HessianCalculus.coordPartial_mul_at (f := chi) (h := multiplierFluxT A m n u) hcd
      ((hFts.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) 0,
    HessianCalculus.coordPartial_mul_at (f := chi) (h := multiplierFluxS A m n u) hcd
      ((hFss.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)) 1] at hcut
  unfold multiplierCutoffError
  linear_combination chi p * hbase - hcut

theorem multiplierCutoffError_contDiffOn
    {A chi m n u : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hm : ContDiffOn ℝ ∞ m U) (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierCutoffError A chi m n u) U := by
  obtain ⟨hFt, hFs⟩ := multiplierFluxes_contDiffOn hU hA hm hn hu
  exact ((partial_contDiffOn hchi hU 0).mul hFt).add ((partial_contDiffOn hchi hU 1).mul hFs)

theorem multiplierCutoffError_zero (A chi m n u : Coord → ℝ) (p : Coord)
    (ht : coordPartial 0 chi p = 0) (hs : coordPartial 1 chi p = 0) :
    multiplierCutoffError A chi m n u p = 0 := by simp [multiplierCutoffError, ht, hs]

theorem directed_source_young_scalar {w f ut us epsilon t R c : ℝ}
    (hw : 0 ≤ w) (hc : 0 < c) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (ht : |t| ≤ R) :
    |f * (w * (-us + epsilon * t * ut))| ≤
      c / 2 * w * (ut^2 + us^2) + ((1 + R^2) / (2 * c)) * w * f^2 := by
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have het : |epsilon * t| ≤ R := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans
      (by have hh := mul_le_mul_of_nonneg_right heps1 hR; simpa only [one_mul] using hh)
  have hsquare : (epsilon * t)^2 ≤ R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (epsilon * t)) het 2
  have hyu := weighted_young c us f hc
  have hyt := weighted_young c ut (epsilon * t * f) hc
  have hraw : |f * (-us + epsilon * t * ut)| ≤
      c / 2 * (ut^2 + us^2) + (1 + R^2) / (2 * c) * f^2 := by
    have htriangle : |f * (-us + epsilon * t * ut)| ≤ |us * f| + |ut * (epsilon * t * f)| := by
      calc
        _ = |-(us * f) + ut * (epsilon * t * f)| := by congr 1; ring
        _ ≤ |us * f| + |ut * (epsilon * t * f)| := by simpa only [abs_neg] using abs_add_le (-(us * f)) (ut * (epsilon * t * f))
    have hproduct := mul_le_mul_of_nonneg_right hsquare (sq_nonneg f)
    have hdiv := div_le_div_of_nonneg_right hproduct (show 0 ≤ 2 * c by positivity)
    calc
      _ ≤ (c * us^2 + f^2 / c) / 2 + (c * ut^2 + (epsilon * t * f)^2 / c) / 2 :=
        htriangle.trans (add_le_add hyu hyt)
      _ = c / 2 * (ut^2 + us^2) + f^2 / (2 * c) + (epsilon * t)^2 * f^2 / (2 * c) := by
        field_simp [hc.ne']
        ring
      _ ≤ c / 2 * (ut^2 + us^2) + f^2 / (2 * c) + R^2 * f^2 / (2 * c) :=
        add_le_add le_rfl hdiv
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_left hraw hw
  calc
    _ = w * |f * (-us + epsilon * t * ut)| := by
      rw [show f * (w * (-us + epsilon * t * ut)) = w * (f * (-us + epsilon * t * ut)) by ring,
        abs_mul, abs_of_nonneg hw]
    _ ≤ w * (c / 2 * (ut^2 + us^2) + (1 + R^2) / (2 * c) * f^2) := hmul
    _ = _ := by ring

end SmoothLocal.Weighted

end

end OAI
