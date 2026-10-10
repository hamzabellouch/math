import OAI.Probability.BenjaminiSchramm.GhostPivotalGeometry

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem twoGhostConnection_le_fan_add_pivotal_sum (hG : Function.Injective G)
    (p : unitInterval) (x : V) (m n : Set V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    law p (finiteGhostConnection G x id m ∩ finiteGhostConnection G x id n) ≤
      law p (DisjointOccurrence (finiteGhostConnection G x id m)
        (finiteGhostConnection G x id n)) +
      ∑' e : E, ∑' u : V, ∑' v : V, ∑' S : Finset V,
        law p {ω | GhostBridgePivotal G ω m n x e u v ∧
          cluster G (ω \ {e}) x = (S : Set V)} := by
  let D := DisjointOccurrence (finiteGhostConnection G x id m) (finiteGhostConnection G x id n)
  let A := fun e u v (S : Finset V) => {ω | GhostBridgePivotal G ω m n x e u v ∧
    cluster G (ω \ {e}) x = (S : Set V)}
  have hsub : (finiteGhostConnection G x id m ∩ finiteGhostConnection G x id n)
      ≤ᵐ[law p] D ∪ ⋃ e, ⋃ u, ⋃ v, ⋃ S, A e u v S := by
    filter_upwards [hfin] with ω hω hm
    rcases two_ghost_connections_or_pivotal G hG ω m n x hm.1 hm.2 with hd | ⟨e,u,v,hp⟩
    · exact Or.inl hd
    · have hf : (cluster G (ω \ {e}) x).Finite :=
        hω.subset (fun _ h => conn_mono G Set.sdiff_subset h)
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨v,
        Set.mem_iUnion.mpr ⟨hf.toFinset,hp,hf.coe_toFinset.symm⟩⟩⟩⟩
  calc
    _ ≤ law p (D ∪ ⋃ e, ⋃ u, ⋃ v, ⋃ S, A e u v S) := measure_mono_ae hsub
    _ ≤ law p D + law p (⋃ e, ⋃ u, ⋃ v, ⋃ S, A e u v S) := measure_union_le _ _
    _ ≤ law p D + ∑' e, law p (⋃ u, ⋃ v, ⋃ S, A e u v S) :=
      add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ law p D + ∑' e, ∑' u, law p (⋃ v, ⋃ S, A e u v S) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum fun e : E => measure_iUnion_le _)
    _ ≤ law p D + ∑' e, ∑' u, ∑' v, law p (⋃ S, A e u v S) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum fun e : E =>
        ENNReal.tsum_le_tsum fun u : V => measure_iUnion_le _)
    _ ≤ _ := add_le_add le_rfl (ENNReal.tsum_le_tsum fun e : E =>
      ENNReal.tsum_le_tsum fun u : V => ENNReal.tsum_le_tsum fun v : V =>
        measure_iUnion_le (fun S : Finset V => A e u v S))

end Percolation.BenjaminiSchramm

end

end OAI
