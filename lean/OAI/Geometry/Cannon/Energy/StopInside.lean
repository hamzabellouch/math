import Mathlib
import OAI.Geometry.Cannon.Energy.ClopenNeighborhoodComponent

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

namespace CannonContinuum

theorem stop_inside {X : Type*} [MetricSpace X]
    {D : Set X} (hD : IsCompact D) (hconn : IsConnected D)
    {p x : X} {r : ℝ} (hx : x ∈ D) (hxr : dist x p < r)
    (hout : ∃ y ∈ D, r < dist y p) :
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ C ⊆ D ∧ x ∈ C ∧
      (∃ z ∈ C, dist z p = r) ∧ ∀ z ∈ C, dist z p ≤ r := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let : PreconnectedSpace D := Subtype.preconnectedSpace hconn.isPreconnected
  let f : D → ℝ := fun z => -dist (z : X) p
  have hf : Continuous f := (continuous_subtype_val.dist continuous_const).neg
  let K : Set D := {z | -r ≤ f z}
  let xK : K := ⟨⟨x,hx⟩,neg_le_neg hxr.le⟩
  have hK : IsClosed K := isClosed_le continuous_const hf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have hbelow : ∃ y : D, f y < -r := by
    obtain ⟨y,hy,hyr⟩ := hout
    exact ⟨⟨y,hy⟩,neg_lt_neg hyr⟩
  obtain ⟨z,hz,hzr⟩ := component_meets_level f hf (-r) xK hbelow
  let g : K → X := fun z => z.val.val
  have hg : Continuous g := continuous_subtype_val.comp continuous_subtype_val
  refine ⟨g '' connectedComponent xK,isClosed_connectedComponent.isCompact.image hg,
    isConnected_connectedComponent.image g hg.continuousOn,?_,?_,?_,?_⟩
  · rintro _ ⟨y,hy,rfl⟩
    exact y.val.property
  · exact ⟨xK,mem_connectedComponent,rfl⟩
  · refine ⟨g z,⟨z,hz,rfl⟩,?_⟩
    exact neg_injective hzr
  · rintro _ ⟨y,hy,rfl⟩
    exact neg_le_neg_iff.mp y.property

end CannonContinuum

end
end
end
end
end
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
