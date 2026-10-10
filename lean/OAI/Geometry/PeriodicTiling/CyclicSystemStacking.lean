import OAI.Geometry.PeriodicTiling.CyclicStack
import OAI.Geometry.PeriodicTiling.FullDifferencePartition

namespace OAI

universe uι uV

namespace PeriodicTilingThree

theorem exists_cyclic_stack_of_system
    {ι : Type uι} [Fintype ι] [Nonempty ι]
    (V : Type uV) [AddCommGroup V] [Finite V] [IsAddCyclic V]
    (F : ι → Finset (Plane × V))
    (hcommon : ∃ A, ∀ ν, Tiles (F ν) A)
    (hnone : ∀ A, (∀ ν, Tiles (F ν) A) → ¬ FullyPeriodic A) :
    ∃ Q : ℕ, 0 < Q ∧
      ∃ T : Finset (Plane × ZMod Q), T.Nonempty ∧
        (∃ B, Tiles T B) ∧ ∀ B, Tiles T B → ¬ FullyPeriodic B := by
  classical
  let s := Fintype.card ι
  have hs : 0 < s := Fintype.card_pos
  let e : ι ≃ Fin s := Fintype.equivFin ι
  let F' : Fin s → Finset (Plane × V) := fun ν => F (e.symm ν)
  have hcommon' : ∃ A, ∀ ν, Tiles (F' ν) A := by
    obtain ⟨A, hA⟩ := hcommon
    exact ⟨A, fun ν => hA (e.symm ν)⟩
  have hnone' : ∀ A, (∀ ν, Tiles (F' ν) A) → ¬ FullyPeriodic A := by
    intro A hA
    apply hnone A
    intro ν
    simpa only [F', Equiv.symm_apply_apply] using hA (e ν)
  obtain ⟨q, hq, hcard, _hfresh, E, hE, hpart, hfull⟩ :=
    exists_fresh_prime_fullDifference_partition s hs ∅ (Nat.card V)
  let havoid : ¬ q ∣ Nat.card V := not_dvd_card_of_lt V hcard
  have hc := cyclicStack_counterexample_of_common_system V q hq havoid
    (F := F') (E := E) hpart hfull hE hcommon' hnone'
  refine ⟨q * Nat.card V, cyclicStackOrder_pos V q hq,
    cyclicStackTile V q hq havoid F' E, hc.1, ?_, hc.2.2⟩
  obtain ⟨A, hA⟩ := hc.2.1
  exact ⟨cyclicStackComplement V q hq havoid A, hA⟩

end PeriodicTilingThree

end OAI
