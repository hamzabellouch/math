import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.TameGraphFlatChart
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

namespace CannonEmbeddedArc.Arc
open Set unitInterval CannonPlanarCorner CannonFaceIncidence

variable {ι D : Type*} [Finite ι] [TopologicalSpace D] [DiscreteTopology D]

lemma tame_edge_incidence_local (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π)
    (i : ι) {t : I} (ht₀ : 0<t) (ht₁ : t<1) :
    ∃ U : Set ℂ, IsOpen U ∧ F i t∈U ∧
      ∃ labels : Bool → D, ∀ x∈U∩(⋃ j, range (F j)),
        incident _ π x=range labels := by
  obtain ⟨H,W,hW,htW,h₀,hflat⟩ := tame_graph_flat_chart F hF Q hQ i ht₀ ht₁
  have he (z : ℂ) : z∈H '' horizontal ↔ (H.symm z).2=0 := by
    rw [H.image_eq_preimage_symm]
    rfl
  obtain ⟨U,hU,h₀U,_,labels,hlabels⟩ := flat_chart_incidence hπ H hW (h₀.symm ▸ htW)
    (fun z hz => by exact not_congr ((hflat z hz).trans (he z)))
  exact ⟨U,hU,h₀ ▸ h₀U,labels,by simpa only [compl_compl] using hlabels⟩

theorem tame_edge_incident_labels (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i, range (F i) ⊆ ⋃ q ∈ Q, segment ℝ q.1 q.2)
    {π : ((⋃ j, range (F j))ᶜ : Set ℂ) → D} (hπ : Continuous π) (i : ι) :
    ∃ labels : Bool → D, ∀ t : I, 0<t → t<1 →
      incident _ π (F i t)=range labels := by
  let A := F i '' Ioo (0:I) 1
  have hA : IsPreconnected A :=
    (isPreconnected_Ioo).image (F i) (F i).continuous.continuousOn
  have hloc : ∀ x∈A, ∃ U : Set ℂ, IsOpen U ∧ x∈U ∧
      ∀ y∈A∩U, incident _ π y=incident _ π x := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨U,hU,htU,labels,hlabels⟩ := tame_edge_incidence_local F hF Q hQ hπ i ht.1 ht.2
    refine ⟨U,hU,htU,?_⟩
    rintro y ⟨⟨s,hs,hsy⟩,hyU⟩
    have hsyG : y∈⋃ j, range (F j) := mem_iUnion.mpr ⟨i,⟨s,hsy⟩⟩
    exact (hlabels y ⟨hyU,hsyG⟩).trans
      (hlabels (F i t) ⟨htU,mem_iUnion.mpr ⟨i,mem_range_self t⟩⟩).symm
  let t₀ : I := ⟨1/2,by constructor <;> norm_num⟩
  have ht₀ : 0<t₀ ∧ t₀<1 := by
    change (0:ℝ)<1/2 ∧ (1/2:ℝ)<1
    norm_num
  obtain ⟨U,hU,htU,labels,hlabels⟩ := tame_edge_incidence_local F hF Q hQ hπ i ht₀.1 ht₀.2
  refine ⟨labels,fun t ht₁ ht₂ => ?_⟩
  exact (incident_constant_on_preconnected hA hloc (F i t) ⟨t,⟨ht₁,ht₂⟩,rfl⟩
    (F i t₀) ⟨t₀,ht₀,rfl⟩).trans
    (hlabels (F i t₀) ⟨htU,mem_iUnion.mpr ⟨i,mem_range_self t₀⟩⟩)
end CannonEmbeddedArc.Arc

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
