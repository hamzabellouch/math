import Mathlib
import OAI.Geometry.Cannon.Energy.PuncturedBallConnected
import OAI.Geometry.Cannon.PlanarGraphs.RegionBoundaryHitsOpen
import OAI.Geometry.Cannon.PlanarGraphs.IncidentSubsetPatch

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

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

namespace CannonPlanarNeighborhood
open Set Metric Topology
open CannonFaceIncidence

theorem open_preconnected_remove_point {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (x : ℂ) : IsPreconnected (U\{x}) := by
  by_cases hx : x∈U
  swap
  · have he : U\{x}=U := by ext z; simp only [mem_sdiff,mem_singleton_iff]; constructor; exact And.left; intro hz; exact ⟨hz,fun h => hx (h ▸ hz)⟩
    rwa [he]
  have hV : IsOpen (U\{x}) := hU.sdiff isClosed_singleton
  let _ : LocallyConnectedSpace (U\{x} : Set ℂ) := hV.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents (U\{x} : Set ℂ)) := inferInstance
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU x hx
  have hsub : ball x r\{x}⊆U\{x} := sdiff_subset_sdiff_left hrU
  obtain ⟨d,hd⟩ := label_on_connected ConnectedComponents.continuous_coe
    (punctured_ball_connected x hr) hsub
  have hi : incident (U\{x}) ConnectedComponents.mk x⊆{d} := by
    apply incident_subset_of_patch isOpen_ball _ (mem_ball_self hr)
    intro y hy
    exact hd ⟨hy.1,hy.2.2⟩
  have hconstant (e : ConnectedComponents (U\{x} : Set ℂ)) : e=d := by
    obtain ⟨z,rfl⟩ := ConnectedComponents.surjective_coe e
    obtain ⟨y,⟨hyU,hyV⟩,hy⟩ := region_boundary_hits_in_open hU hV sdiff_subset hc
      ⟨x,hx,fun h => h.2 (mem_singleton x)⟩ ConnectedComponents.continuous_coe
      (ConnectedComponents.mk z) ⟨z,z.property,rfl⟩
    have hyx : y=x := by by_contra hn; exact hyV ⟨hyU,hn⟩
    subst y
    exact hi hy
  have : PreconnectedSpace (U\{x} : Set ℂ) := by
    rw [preconnectedSpace_iff_connectedComponent]
    intro a
    apply eq_univ_of_forall
    intro b
    exact ConnectedComponents.coe_eq_coe'.mp ((hconstant _).trans (hconstant _).symm)
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

theorem open_preconnected_remove_finite {U : Set ℂ} (hU : IsOpen U)
    (hc : IsPreconnected U) (T : Finset ℂ) : IsPreconnected (U\(T:Set ℂ)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hc
  | @insert x T hx ih =>
    have he : U\(↑(insert x T):Set ℂ)=(U\(T:Set ℂ))\{x} := by ext z; simp; tauto
    rw [he]
    exact open_preconnected_remove_point (hU.sdiff T.finite_toSet.isClosed) ih x
end CannonPlanarNeighborhood

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
end
end
end
end

end OAI
