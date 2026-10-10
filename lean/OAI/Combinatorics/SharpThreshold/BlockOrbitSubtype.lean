import OAI.Combinatorics.SharpThreshold.BlockOrbits
import OAI.Combinatorics.SharpThreshold.BlockRestrictionSymmetry

namespace OAI

noncomputable section
namespace Problem313

/-- The supported permutation orbit of a free edge consists only of free edges. -/
theorem blockEdgeOrbit_touches {n : ℕ} {B : Finset (Fin n)}
    {e d : GraphEdge n} (he : EdgeTouches B e) (hd : d ∈ blockEdgeOrbit B e) :
    EdgeTouches B d := by
  obtain ⟨π, hπ, rfl⟩ := mem_blockEdgeOrbit.mp hd
  exact (edgeTouches_permEdge_iff hπ e).mpr he

/-- A free edge has at least `B.card` free-edge orbit mates, with explicit
supported-permutation witnesses. This is the finite-coordinate interface for
conditional influence bounds. -/
theorem exists_freeEdge_orbit_family {n : ℕ} (B : Finset (Fin n))
    (hB : 3 ≤ B.card) (e : {e : GraphEdge n // EdgeTouches B e}) :
    ∃ S : Finset {d : GraphEdge n // EdgeTouches B d},
      B.card ≤ S.card ∧ ∀ d ∈ S, ∃ π : Equiv.Perm (Fin n),
        SupportedOnBlock B π ∧ permEdge π e.val = d.val := by
  classical
  let S := (blockEdgeOrbit B e.val).subtype (EdgeTouches B)
  have hmap : S.map (Function.Embedding.subtype _) = blockEdgeOrbit B e.val :=
    Finset.subtype_map_of_mem (fun d hd => blockEdgeOrbit_touches e.property hd)
  have hcard : S.card = (blockEdgeOrbit B e.val).card := by
    simpa using congrArg Finset.card hmap
  refine ⟨S, ?_, ?_⟩
  · rw [hcard]
    apply blockEdgeOrbit_card_lower hB
    obtain ⟨v, hve, hvB⟩ := e.property
    exact ⟨v, Finset.mem_inter.mpr ⟨hve, hvB⟩⟩
  · intro d hd
    exact mem_blockEdgeOrbit.mp (Finset.mem_subtype.mp hd)

end Problem313

end

end OAI
