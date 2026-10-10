import OAI.Geometry.Relativity.CKS.SchwarzschildHorizonExclusionDefinitions

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff
namespace CKSSchwarzschild
open CKSBoundarySurface
universe u
structure IntrinsicInteriorImmersion (m : ℝ) (T : Type u)
    [TopologicalSpace T] [ChartedSpace E2 T] where
  map : T → Exterior
  smooth : ContMDiff I2 I3 ∞ map
  immersion : ∀ p, Function.Injective (mfderiv I2 I3 map p)
  interior : ∀ p, map p ∈ I3.interior Exterior
  normal : ∀ p, TangentSpace I3 (map p)
  normal_unit : ∀ p, metricInner m (map p) (normal p) (normal p) = 1
  normal_orthogonal : ∀ p a, metricInner m (map p) (normal p) (mfderiv I2 I3 map p a) = 0

variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T]
def intrinsicCoordinateMap {m : ℝ} (D : IntrinsicInteriorImmersion m T) : T → E3 :=
  position m ∘ D.map
def intrinsicCoordinateNormal {m : ℝ} (D : IntrinsicInteriorImmersion m T) : T → E3 :=
  fun p => mfderiv I3 𝓘(ℝ,E3) (position m) (D.map p) (D.normal p)
def intrinsicSurfaceMeanCurvature {m : ℝ} (D : IntrinsicInteriorImmersion m T) (p : T) : ℝ :=
  surfaceMeanCurvature m (intrinsicCoordinateMap D) (intrinsicCoordinateNormal D) p
def intrinsicSurfaceTensorTrace {m : ℝ} (D : IntrinsicInteriorImmersion m T) (p : T) : ℝ :=
  surfaceTensorTrace m (intrinsicCoordinateMap D) p
end CKSSchwarzschild

end

end OAI
