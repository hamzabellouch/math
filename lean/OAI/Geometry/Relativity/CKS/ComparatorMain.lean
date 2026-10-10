import OAI.Geometry.Relativity.CKS.Main

namespace OAI
noncomputable section
namespace CKSMain
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
universe u v
attribute [local instance] manifold_regular sixteen_atLeastTwo

theorem schwarzschild_equality_examples (m : ℝ) (hm : 0 < m) :
    SchwarzschildExample.{v} m hm := by
  exact ⟨CKSSchwarzschild.smoothMetric hm, CKSSchwarzschild.cksData hm,
    schwarzschildAtlas hm, fun _ => rfl, schwarzschild_attainment hm⟩


end CKSMain
end
end OAI
