import Mathlib
import OAI.Geometry.Cannon.Energy.Extend

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonChart

def onInterior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X → Y) (he : IsEmbedding e) (f : C(X,ℝ)) : C(interior (range e),ℝ) :=
  ⟨fun z => extend e f z.val,
    (continuousOn_extend e he f f.continuous).comp_continuous
      continuous_subtype_val (fun z => interior_subset z.property)⟩

lemma onInterior_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X → Y) (he : IsEmbedding e) (f : C(X,ℝ)) (z : X)
    (hz : e z ∈ interior (range e)) :
    onInterior e he f ⟨e z,hz⟩ = f z := extend_apply e he.injective f z

end CannonChart

end
end
end
end
end
end
end
end
end

end OAI
