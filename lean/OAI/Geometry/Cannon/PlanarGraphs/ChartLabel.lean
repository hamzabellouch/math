import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.Region

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonFaceIncidence
open Set Topology

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]
variable {Y : Type*} [TopologicalSpace Y]
def chartLabel (e : Y → X) {V : Set X} (π : V → D) : (e ⁻¹' V) → D :=
  fun x => π ⟨e x.val,x.property⟩

omit [DiscreteTopology D] in
lemma chartLabel_continuous (e : Y → X) (he : Continuous e) {V : Set X}
    {π : V → D} (hπ : Continuous π) : Continuous (chartLabel e π) :=
  hπ.comp ((he.comp continuous_subtype_val).subtype_mk _)

omit [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D] [TopologicalSpace Y] in
lemma region_chartLabel (e : Y → X) {V : Set X} (π : V → D) (d : D) :
    region _ (chartLabel e π) d=e ⁻¹' region V π d := by
  ext x
  rfl

omit [TopologicalSpace D] [DiscreteTopology D] in
lemma incident_chartLabel (e : Y → X) (he : IsOpenMap e) (hc : Continuous e)
    {V : Set X} (π : V → D) (x : Y) :
    incident _ (chartLabel e π) x=incident V π (e x) := by
  ext d
  change x∈closure (region _ (chartLabel e π) d) ↔ e x∈closure (region V π d)
  rw [region_chartLabel]
  rw [← he.preimage_closure_eq_closure_preimage hc (region V π d)]
  rfl

omit [TopologicalSpace Y] in
lemma chartLabel_surjective (e : Y → X) (he : DenseRange e) {V : Set X}
    (hV : IsOpen V) {π : V → D} (hπ : Continuous π) (hsur : Function.Surjective π) :
    Function.Surjective (chartLabel e π) := by
  intro d
  obtain ⟨x,hx⟩ := hsur d
  obtain ⟨y,hy,hyd⟩ := he.exists_mem_open (region_isOpen hV hπ d) ⟨x.val,x.property,hx⟩
  exact ⟨⟨y,hy⟩,hyd⟩
end CannonFaceIncidence

namespace CannonFaceIncidence
open Set Topology

variable {X Y D : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace D] [DiscreteTopology D]

def labelPull (e : Y → X) {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V)
    (π : V → D) : W → D := chartLabel e π ∘ (Homeomorph.setCongr hW)

omit [DiscreteTopology D] in
lemma labelPull_continuous (e : Y → X) (he : Continuous e)
    {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V) {π : V → D} (hπ : Continuous π) :
    Continuous (labelPull e hW π) :=
  (chartLabel_continuous e he hπ).comp (Homeomorph.setCongr hW).continuous

omit [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D] in
lemma region_labelPull (e : Y → X) {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V)
    (π : V → D) (d : D) : region W (labelPull e hW π) d=e ⁻¹' region V π d := by
  subst W
  exact region_chartLabel e π d

omit [TopologicalSpace D] [DiscreteTopology D] in
lemma incident_labelPull (e : Y → X) (he : IsOpenMap e) (hc : Continuous e)
    {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V) (π : V → D) (x : Y) :
    incident W (labelPull e hW π) x=incident V π (e x) := by
  ext d
  change x∈closure (region W (labelPull e hW π) d) ↔ e x∈closure (region V π d)
  rw [region_labelPull, ← he.preimage_closure_eq_closure_preimage hc (region V π d)]
  rfl

lemma labelPull_surjective (e : Y → X) (he : DenseRange e)
    {V : Set X} {W : Set Y} (hW : W=e ⁻¹' V) (hV : IsOpen V)
    {π : V → D} (hπ : Continuous π) (hsur : Function.Surjective π) :
    Function.Surjective (labelPull e hW π) :=
  (chartLabel_surjective e he hV hπ hsur).comp (Homeomorph.setCongr hW).surjective
end CannonFaceIncidence

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
end

end OAI
