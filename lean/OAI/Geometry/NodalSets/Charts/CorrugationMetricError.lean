import OAI.Geometry.NodalSets.Elliptic.CorrugationScaledJetsLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma localizedCorrugation_first_scaled (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ)
    (a b : Coord →L[ℝ] ℝ) (y x v : Coord) :
    fderiv ℝ (localizedCorrugation χ f s J R a b y) x v =
      s*χ (R⁻¹ • (x-y))*fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v) +
      s/(J*R)*f (corrugationFastMap J a b (x-y))*fderiv ℝ χ (R⁻¹ • (x-y)) v := by
  rw [localizedCorrugation_first χ f hχ hf]
  simp only [corrugationSlowMap,corrugationFastMap,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  by_cases hR : R = 0
  · simp [hR]
    field_simp
  · field_simp
    ring

lemma localizedCorrugation_second_scaled (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ)
    (a b : Coord →L[ℝ] ℝ) (y x u v : Coord) :
    fderiv ℝ (fderiv ℝ (localizedCorrugation χ f s J R a b y)) x u v =
      s*J*χ (R⁻¹ • (x-y))*
        fderiv ℝ (fderiv ℝ f) (corrugationFastMap J a b (x-y)) (a.prod b u) (a.prod b v) +
      s/R*(fderiv ℝ χ (R⁻¹ • (x-y)) v*
        fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b u) +
        fderiv ℝ χ (R⁻¹ • (x-y)) u*
        fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v)) +
      s/(J*R^2)*f (corrugationFastMap J a b (x-y))*
        fderiv ℝ (fderiv ℝ χ) (R⁻¹ • (x-y)) u v := by
  rw [localizedCorrugation_second χ f hχ hf]
  simp only [corrugationSlowMap,corrugationFastMap,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  by_cases hR : R = 0
  · simp [hR]
    field_simp
  · field_simp
    ring

def corrugationMetricError (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ) (s J R : ℝ)
    (a b : Coord →L[ℝ] ℝ) (y x u v : Coord) : ℝ :=
  s/R*(fderiv ℝ χ (R⁻¹ • (x-y)) v*
    fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b u) +
    fderiv ℝ χ (R⁻¹ • (x-y)) u*
    fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v)) +
  s/(J*R^2)*f (corrugationFastMap J a b (x-y))*
    fderiv ℝ (fderiv ℝ χ) (R⁻¹ • (x-y)) u v -
  s*χ (R⁻¹ • (x-y))*fderiv ℝ f (corrugationFastMap J a b (x-y))
    (a.prod b (metricConnection (g x) (fderiv ℝ g x) u v)) -
  s/(J*R)*f (corrugationFastMap J a b (x-y))*
    fderiv ℝ χ (R⁻¹ • (x-y)) (metricConnection (g x) (fderiv ℝ g x) u v)

lemma localizedCorrugation_metric_hessian (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ)
    (a b : Coord →L[ℝ] ℝ) (y x u v : Coord) :
    sourceHessian g (localizedCorrugation χ f s J R a b y) x u v =
      s*J*χ (R⁻¹ • (x-y))*
        fderiv ℝ (fderiv ℝ f) (corrugationFastMap J a b (x-y)) (a.prod b u) (a.prod b v) +
      corrugationMetricError g χ f s J R a b y x u v := by
  rw [sourceHessian_apply,localizedCorrugation_second_scaled χ f hχ hf s hJ,
    localizedCorrugation_first_scaled χ f hχ hf s hJ]
  unfold corrugationMetricError
  ring

end
end Yau.Geometry

end OAI
