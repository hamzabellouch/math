import OAI.Geometry.PeriodicTiling.CommonModel
import OAI.Geometry.PeriodicTiling.EncodedSystem

namespace OAI

noncomputable section

namespace PeriodicTilingThree.CommonModel

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem ordinaryActivationMap_outputs (n : Column p) (b : Base E) :
    ordinaryActivationMap E n (outputs E) b =
      ordinaryForward E n b.1 (b.2 (.inl n)) := by
  funext j
  simp [ordinaryActivationMap, ordinarySource, activationSource, outputs, ordinaryForward]

theorem seedActivationMap_outputs (t : Fin 2) (b : Base E) :
    seedActivationMap E t (outputs E) b = seedActualForward E t b.1 b.2 := by
  rfl

theorem common_solution : Solves E (commonGraph E) := by
  apply (solves_iff E (commonGraph E)).mpr
  refine ⟨commonGraph_tiles_kernel E, ?_, ?_, ?_, ?_, ?_⟩
  · exact (dependenceTiles_iff E (outputs E)).mpr (outputs_hasDependence E)
  · exact (wordConstraintTiles_iff E (outputs E) (outputs_hasDependence E)).mpr
      (active_word_allowed E)
  · apply (seedConstraintTiles_iff E (outputs E) (outputs_hasDependence E)).mpr
    intro t n x j ht hj
    exact active_seed_forces_symbol E t n x j ht hj
  · intro n
    apply (ordinaryActivationTile_iff E n (outputs E)).mpr
    intro b
    rw [ordinaryActivationMap_outputs]
    exact ordinaryForward_bijective E n b.1 (b.2 (.inl n))
  · intro t
    apply (seedActivationTile_iff E t (outputs E)).mpr
    intro b
    rw [seedActivationMap_outputs]
    exact seedActualForward_bijective E t b.1 b.2

theorem commonGraph_tiles_testTile (i : TestIndex E) :
    Tiles (testTile E i) (commonGraph E) :=
  (solves_iff_index E (commonGraph E)).mp (common_solution E) i

end PeriodicTilingThree.CommonModel

namespace PeriodicTilingThree

theorem exists_common_solution {p : ℕ} [NeZero p] (E : EncodingParameters p) :
    ∃ A : Set (Ambient E), Solves E A :=
  ⟨CommonModel.commonGraph E, CommonModel.common_solution E⟩

end PeriodicTilingThree

end

end OAI
