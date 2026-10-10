import OAI.Geometry.EinsteinFour.WeylGeometry
import Mathlib.Geometry.Manifold.Riemannian.Basic

namespace OAI

/-! The actual tangent norm and path distance of a smooth metric. These
basic definitions are independent of the classification and scaling steps. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def metricTangentNorm (g : SmoothMetric M) (x : M) (v : TangentSpace I4 x) : ℝ :=
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  ‖v‖

def metricTangentENorm (g : SmoothMetric M) (x : M) (v : TangentSpace I4 x) : ℝ≥0∞ :=
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  ‖v‖ₑ

theorem metricTangentNorm_eq_sqrt (g : SmoothMetric M) (x : M)
    (v : TangentSpace I4 x) : metricTangentNorm g x v = Real.sqrt (g.inner x v v) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact norm_eq_sqrt_real_inner v

theorem metricTangentENorm_eq_ofReal (g : SmoothMetric M) (x : M)
    (v : TangentSpace I4 x) :
    metricTangentENorm g x v = ENNReal.ofReal (metricTangentNorm g x v) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact (ofReal_norm v).symm

def metricEDistance (g : SmoothMetric M) (x y : M) : ℝ≥0∞ :=
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I4 x y

theorem metricEDistance_eq_iInf (g : SmoothMetric M) (x y : M) :
    metricEDistance g x y =
      ⨅ (γ : Path x y) (_ : ContMDiff (𝓡∂ 1) I4 1 γ),
        ∫⁻ t, metricTangentENorm g (γ t) (mfderiv (𝓡∂ 1) I4 γ t 1) := by
  simp only [metricEDistance, Manifold.riemannianEDist, metricTangentENorm]

end
end PositiveEinsteinFour.Geometry

end OAI
