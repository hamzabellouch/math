import OAI.Geometry.PeriodicTiling.CommonSolution
import OAI.Geometry.PeriodicTiling.EncodedSystemObstruction
import OAI.Geometry.PeriodicTiling.EncodingPrimeSelection
import OAI.Geometry.PeriodicTiling.CyclicFactorCRT
import OAI.Geometry.PeriodicTiling.CyclicSystemStacking

namespace OAI

namespace PeriodicTilingThree

theorem cyclic_counterexample_of_parameters {p : ℕ} [NeZero p]
    (E : EncodingParameters p) :
    ∃ Q : ℕ, 0 < Q ∧
      ∃ F : Finset (Plane × ZMod Q), F.Nonempty ∧
        (∃ A, Tiles F A) ∧ ∀ A, Tiles F A → ¬ FullyPeriodic A := by
  classical
  let : IsAddCyclic (V E) := isAddCyclic_of_surjective
    (finiteFactorEquiv E).symm (finiteFactorEquiv E).symm.surjective
  apply exists_cyclic_stack_of_system (V E) (testTile E)
  · exact ⟨CommonModel.commonGraph E, CommonModel.commonGraph_tiles_testTile E⟩
  · intro A hA
    exact testTile_not_fully_periodic E hA

theorem exists_cyclic_counterexample :
    ∃ Q : ℕ, 0 < Q ∧
      ∃ F : Finset (Plane × ZMod Q), F.Nonempty ∧
        (∃ A, Tiles F A) ∧ ∀ A, Tiles F A → ¬ FullyPeriodic A := by
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes 201
  let : NeZero p := ⟨hp.ne_zero⟩
  let E : EncodingParameters p := encodingParameters hp (by omega)
  exact cyclic_counterexample_of_parameters E

end PeriodicTilingThree

end OAI
