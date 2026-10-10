import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphActionCoordinates
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E Λ Q Y : Type*} (G : BondGraph V E)
  [Group Λ] [Group Q] [MulAction Λ V] [MulAction Λ E]

lemma finite_kernel_orbits_from_one_vertex
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ)) (ρ : Λ →* Q) (o : V)
    (ho : (MulAction.orbit ρ.ker o).Finite) :
    ∀ v : V, (MulAction.orbit ρ.ker v).Finite := by
  intro v
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc o v)
  have hfin := ho.biUnion (fun w _ => G.vertexBall_finite hl w n)
  apply hfin.subset
  rintro w ⟨g,rfl⟩
  refine Set.mem_iUnion₂.mpr ⟨g.val • o,⟨g,rfl⟩,?_⟩
  exact (Aut.vertexBall_mem G (G.smulAut ha g.val) o v n).mpr hn

lemma finite_subgroup_of_finite_orbit_stabilizer [MulAction Q Y]
    (J : Subgroup Q) (y : Y) (ho : (MulAction.orbit J y).Finite)
    (hs : (MulAction.stabilizer Q y : Set Q).Finite) : (J : Set Q).Finite := by
  have hstab : (MulAction.stabilizer J y : Set J).Finite := by
    apply (Set.Finite.preimage Subtype.val_injective.injOn hs).subset
    exact fun _ h => h
  let _ := ho.to_subtype
  let _ := hstab.to_subtype
  let _ : Finite J := Finite.of_equiv _ (MulAction.orbitProdStabilizerEquivGroup J y)
  exact Set.toFinite _

lemma finite_stabilizer_images_from_orbit_quotient [MulAction Q Y]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ)) (ρ : Λ →* Q)
    (o : V) (pi : V → Y) (y : Y)
    (hpi : ∀ g : Λ, pi (g • o)=ρ g • y)
    (hy : (MulAction.stabilizer Q y : Set Q).Finite) :
    ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set Q).Finite := by
  intro v
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc v o)
  apply finite_subgroup_of_finite_orbit_stabilizer _ y _ hy
  apply ((G.vertexBall_finite hl v n).image pi).subset
  rintro z ⟨g,rfl⟩
  obtain ⟨a,ha',hga⟩ := g.property
  refine ⟨a • o,?_,?_⟩
  · have hh := (Aut.vertexBall_mem G (G.smulAut ha a) v o n).mpr hn
    change a • o ∈ G.vertexBall (a • v) n at hh
    exact ha' ▸ hh
  · have hh := hpi a
    rw [hga] at hh
    exact hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
