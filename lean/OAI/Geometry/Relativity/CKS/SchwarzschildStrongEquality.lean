import OAI.Geometry.Relativity.CKS.SchwarzschildEquality
import OAI.Geometry.Relativity.CKS.SchwarzschildHorizonExclusion

namespace OAI

noncomputable section
namespace CKSSchwarzschild
open CKSBoundarySurface
open scoped ContDiff
universe u

theorem schwarzschild_equality_without_closed_horizons {m : ℝ} (hm : 0 < m) :
    SchwarzschildEqualityExample m hm ∧
    ∀ (T : Type u) [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]
      [CompactSpace T] [Nonempty T] (D : InteriorImmersion m T),
      ¬ (∀ p, surfaceMeanCurvature m D.map D.normal p + surfaceTensorTrace m D.map p = 0 ∨
        surfaceMeanCurvature m D.map D.normal p - surfaceTensorTrace m D.map p = 0) := by
  refine ⟨schwarzschild_equality_example hm,?_⟩
  intro T _ _ _ _ _ D
  exact no_closed_apparent_horizon hm D
end CKSSchwarzschild

end

end OAI
