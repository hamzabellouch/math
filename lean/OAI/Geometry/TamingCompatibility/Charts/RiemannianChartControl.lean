import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.CompactCutoff
import OAI.Geometry.TamingCompatibility.DifferentialForms.RiemannianSmoothLipschitz
import OAI.Geometry.TamingCompatibility.Charts.ScalarChartLift

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms Set Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]

theorem compact_chart_distance_control (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ L : ℝ≥0, 0 < L ∧ ∀ x y : X,
      x ∈ (extChartAt Model p).source → y ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → extChartAt Model p y ∈ K →
      edist (extChartAt Model p x) (extChartAt Model p y) ≤
        L * Manifold.riemannianEDist Model x y := by
  obtain ⟨φ,hφ,hφT,hφone⟩ := SchwartzCutoff.exists_one_on_compact hK
    (isOpen_extChartAt_target p) hKT
  let f : Space → Space := fun z => φ z • z
  have hfs : ContDiff ℝ ∞ f := (φ.smooth ⊤).smul contDiff_id
  have hfc : HasCompactSupport f := hφ.smul_right
  have hfT : tsupport f ⊆ (extChartAt Model p).target :=
    (tsupport_smul_subset_left φ id).trans hφT
  obtain ⟨L,hL,hbound⟩ := smooth_lipschitz_riemannian
    (vectorChartLift_smooth p hfs hfc hfT)
  refine ⟨L,hL,?_⟩
  intro x y hxs hys hxK hyK
  have he (z : X) (hzs : z ∈ (extChartAt Model p).source)
      (hzK : extChartAt Model p z ∈ K) :
      vectorChartLift p f z = extChartAt Model p z := by
    simp only [vectorChartLift,ite_eq_left hzs,f,hφone _ hzK,one_smul]
  simpa only [he x hxs hxK,he y hys hyK] using hbound x y
end TamingCompatibility

end

end OAI
