import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildEqualityDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildAreaDefinitions
import OAI.Geometry.Relativity.CKS.BoundaryBridge

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u v
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

namespace InteriorSurface
variable {q : SmoothMetric I3 (M := N)} {k : InnerField I3 (M := N)}
  {A : CoefficientAtlas q k} {T : Type v} [TopologicalSpace T] [ChartedSpace E2 T]
  [IsManifold I2 ∞ T] (D : InteriorSurface q k A T)

lemma ComponentwiseApparent.pointwise (h : D.ComponentwiseApparent) (p : T) :
    D.thetaPlus p = 0 ∨ D.thetaMinus p = 0 := by
  rcases h p with h | h
  · exact Or.inl (h p mem_connectedComponent)
  · exact Or.inr (h p mem_connectedComponent)

end InteriorSurface

attribute [local instance] sixteen_atLeastTwo

def SchwarzschildAttainment (m : ℝ) (hm : 0 < m) : Prop :=
  MainHypotheses.{0,v} (CKSSchwarzschild.smoothMetric hm) (CKSSchwarzschild.tensorInner m)
    (CKSSchwarzschild.cksData hm) (schwarzschildAtlas hm) ∧
  CKSSchwarzschild.HorizonRegularGraph m ∧
  bondiMass (CKSSchwarzschild.cksData hm) = m ∧
  minimumEnclosingArea (CKSSchwarzschild.smoothMetric hm) = 16*Real.pi*m^2 ∧
  bondiMass (CKSSchwarzschild.cksData hm) =
    Real.sqrt (minimumEnclosingArea (CKSSchwarzschild.smoothMetric hm) / (16*Real.pi))

end CKSMain

end

end OAI
