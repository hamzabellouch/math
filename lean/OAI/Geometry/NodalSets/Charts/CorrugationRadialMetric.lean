import OAI.Geometry.NodalSets.Charts.CorrugationMetricError
import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma localizedCorrugation_radial_first (χ : Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (amp s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ) (a b : Coord →L[ℝ] ℝ)
    (y x v : Coord) (m : ℤ × ℤ) (z : ℝ × ℝ) {r : ℝ}
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) (hr : r ≠ 0)
    (hz : r^2=z.1^2+z.2^2)
    (he : corrugationFastMap J a b (x-y) = (z.1+(m.1:ℝ),z.2+(m.2:ℝ))) :
    fderiv ℝ (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x v =
      s*χ (R⁻¹ • (x-y))*corrugationSlope amp (1/4) r*radialComponent z (a.prod b v) r +
      s/(J*R)*corrugationPeriodicWell amp (corrugationFastMap J a b (x-y))*
        fderiv ℝ χ (R⁻¹ • (x-y)) v := by
  rw [localizedCorrugation_first_scaled χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ]
  rw [he,(corrugationPeriodicWell_radial_jets amp m z hz₁ hz₂ hr hz (a.prod b v) (a.prod b v)).1]
  ring

lemma localizedCorrugation_radial_hessian (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (χ : Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (amp s : ℝ) {J : ℝ} (hJ : J ≠ 0) (R : ℝ) (a b : Coord →L[ℝ] ℝ)
    (y x u v : Coord) (m : ℤ × ℤ) (z : ℝ × ℝ) {r : ℝ}
    (hz₁ : |z.1| < 1/2) (hz₂ : |z.2| < 1/2) (hr : r ≠ 0)
    (hz : r^2=z.1^2+z.2^2)
    (he : corrugationFastMap J a b (x-y) = (z.1+(m.1:ℝ),z.2+(m.2:ℝ))) :
    sourceHessian g (localizedCorrugation χ (corrugationPeriodicWell amp) s J R a b y) x u v =
      s*J*χ (R⁻¹ • (x-y))*(
        deriv (corrugationSlope amp (1/4)) r*radialComponent z (a.prod b u) r*radialComponent z (a.prod b v) r +
        (corrugationSlope amp (1/4) r/r)*angularComponent z (a.prod b u) r*angularComponent z (a.prod b v) r) +
      corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x u v := by
  rw [localizedCorrugation_metric_hessian g χ _ hχ (corrugationPeriodicWell_smooth amp) s hJ]
  congr 1
  rw [he,(corrugationPeriodicWell_radial_jets amp m z hz₁ hz₂ hr hz (a.prod b u) (a.prod b v)).2]

end
end Yau.Geometry

end OAI
