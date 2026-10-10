import OAI.Geometry.PeriodicTiling.EncodedSystem
import OAI.Geometry.PeriodicTiling.Activation
import OAI.Geometry.PeriodicTiling.SystemObstruction

namespace OAI

namespace PeriodicTilingThree

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

theorem solves_not_fully_periodic {A : Set (Ambient E)} (hA : Solves E A) :
    ¬ FullyPeriodic A := by
  obtain ⟨o, rfl⟩ := exists_graph_of_solves E hA
  obtain ⟨_hg, hd, hw, hs, ho, ht⟩ := (solves_iff E (graph o)).mp hA
  have hdep : HasDependence E o := (dependenceTiles_iff E o).mp hd
  apply graph_not_fully_periodic_of_activity E o hdep
  · exact (wordConstraintTiles_iff E o hdep).mp hw
  · exact (seedConstraintTiles_iff E o hdep).mp hs
  · intro n
    exact ordinary_active_of_tile E o hdep n (ho n)
  · intro t
    exact seed_active_somewhere_of_tile E o hdep t (ht t)

theorem testTile_not_fully_periodic {A : Set (Ambient E)}
    (hA : ∀ i : TestIndex E, Tiles (testTile E i) A) : ¬ FullyPeriodic A :=
  solves_not_fully_periodic E ((solves_iff_index E A).mpr hA)

theorem no_periodic_common_solution :
    ¬ ∃ A : Set (Ambient E), Solves E A ∧ FullyPeriodic A := by
  rintro ⟨A, hA, hperiod⟩
  exact solves_not_fully_periodic E hA hperiod

end PeriodicTilingThree

end OAI
