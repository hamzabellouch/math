import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildMetricDefinitions
import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

attribute [local instance] CKSInducedArea.real_continuousAdd CKSInducedArea.real_smulCommClass
  CKSInducedArea.real_continuousConstSMul CKSBoundarySurface.two_atLeastTwo

attribute [local instance] OAI.CKSSchwarzschild.frameCovectorModule

def parameterSecondForm (m : ℝ) (f : E2 → E3) (y : E2) (N : E3) (a b : E2) : ℝ :=
  -(cartMetric m (f y) N (fderiv ℝ (fun z => fderiv ℝ f z b) y a) +
    christoffelPair (cartMetric m) (f y) (fderiv ℝ f y a) (fderiv ℝ f y b) N)

def parameterMeanCurvature (m : ℝ) (f : E2 → E3) (y : E2) (N : E3) : ℝ :=
  let a := firstFrame (cartMetric m (f y)) (fderiv ℝ f y)
  let b := secondFrame (cartMetric m (f y)) (fderiv ℝ f y)
  parameterSecondForm m f y N a a + parameterSecondForm m f y N b b

def parameterTensorTrace (m : ℝ) (f : E2 → E3) (y : E2) : ℝ :=
  let a := fderiv ℝ f y (firstFrame (cartMetric m (f y)) (fderiv ℝ f y))
  let b := fderiv ℝ f y (secondFrame (cartMetric m (f y)) (fderiv ℝ f y))
  cartTensor m (f y) a a + cartTensor m (f y) b b

universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T]

def surfaceParameter (F : T → E3) (p : T) : E2 → E3 := F ∘ (extChartAt I2 p).symm

def surfaceMeanCurvature (m : ℝ) (F N : T → E3) (p : T) : ℝ :=
  parameterMeanCurvature m (surfaceParameter F p) ((extChartAt I2 p) p) (N p)

def surfaceTensorTrace (m : ℝ) (F : T → E3) (p : T) : ℝ :=
  parameterTensorTrace m (surfaceParameter F p) ((extChartAt I2 p) p)

structure InteriorImmersion (m : ℝ) (T : Type u) [TopologicalSpace T] [ChartedSpace E2 T] where
  map : T → E3
  smooth : ContMDiff I2 𝓘(ℝ,E3) ∞ map
  immersion : ∀ p, Function.Injective (mfderiv I2 𝓘(ℝ,E3) map p)
  interior : ∀ p, 2*m < ‖map p‖
  normal : T → E3
  normal_unit : ∀ p, cartMetric m (map p) (normal p) (normal p) = 1
  normal_orthogonal : ∀ p a, cartMetric m (map p) (normal p) (mfderiv I2 𝓘(ℝ,E3) map p a) = 0

end CKSSchwarzschild

end

end OAI
