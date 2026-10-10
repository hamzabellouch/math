import OAI.Geometry.NodalSets.Charts.CorrugationRadialMetric
import OAI.Geometry.NodalSets.Elliptic.CorrugationAssembly

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma sourceHessian_add (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S w : Coord → ℝ) (hS : ContDiff ℝ ∞ S) (hw : ContDiff ℝ ∞ w) (x u v : Coord) :
    sourceHessian g (S+w) x u v = sourceHessian g S x u v+sourceHessian g w x u v := by
  have he : fderiv ℝ (S+w) = fderiv ℝ S+fderiv ℝ w := by
    funext y
    exact fderiv_add (hS.differentiable (by simp) y) (hw.differentiable (by simp) y)
  simp only [sourceHessian_apply,he]
  rw [fderiv_add ((hS.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hw.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)]
  simp
  ring

lemma metricGradient_add (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S w : Coord → ℝ) {x : Coord} (hS : DifferentiableAt ℝ S x) (hw : DifferentiableAt ℝ w x) : metricGradient g (S+w) x = metricGradient g S x+metricGradient g w x := by
  unfold metricGradient
  rw [fderiv_add hS hw,map_add]

lemma corrugated_envelope_radial_hessian
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (S χ : Coord → ℝ) (hS : ContDiff ℝ ∞ S) (hχ : ContDiff ℝ ∞ χ)
    (amp s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ) (a b : Coord →L[ℝ] ℝ)
    (y x u v : Coord) (m : ℤ × ℤ) (z : ℝ × ℝ) {r : ℝ}
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) (hr : r ≠ 0)
    (hz : r^2=z.1^2+z.2^2)
    (he : corrugationFastMap J a b (x-y) = (z.1+(m.1:ℝ),z.2+(m.2:ℝ))) :
    sourceHessian g (S+localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x u v =
      sourceHessian g S x u v + s*J*χ (R⁻¹ • (x-y))*(
        deriv (corrugationSlope amp (1/4)) r*radialComponent z (a.prod b u) r*radialComponent z (a.prod b v) r +
        (corrugationSlope amp (1/4) r/r)*angularComponent z (a.prod b u) r*angularComponent z (a.prod b v) r) +
      corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x u v := by
  rw [sourceHessian_add g S _ hS (localizedCorrugation_smooth χ _ hχ (corrugationPeriodicWell_smooth amp) _ _ _ _ _ _),
    localizedCorrugation_radial_hessian g χ hχ amp s hJ R a b y x u v m z hz₁ hz₂ hr hz he]
  ring

end
end Yau.Geometry

end OAI
