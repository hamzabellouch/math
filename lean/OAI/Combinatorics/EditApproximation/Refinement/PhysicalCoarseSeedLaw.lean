import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedTables
import OAI.Combinatorics.EditApproximation.Coarse.CoarseGlobalSeed
import OAI.Combinatorics.EditApproximation.Geometry.StateDomain
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The clamped incoming seed table is the image of the actual complete
coarse sampler. Its simultaneous initial accuracy is a derived fact. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section CoarseLaw

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (N B : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)





variable [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]

noncomputable def physicalCoarseSeedLaw : Measure (ClampedPhysicalSeed M J target.length N) := by
  classical
  exact (coarseFullSeedMeasure B depth
    (fun state : PhysicalEntry M J target.length => physicalSource source state.1)
    (fun state : PhysicalEntry M J target.length => substring target state.2.lo state.2.hi)).map
      (physicalCoarseSeedTable source target N B depth)

instance physicalCoarseSeedLaw_probability :
    IsProbabilityMeasure (physicalCoarseSeedLaw source target N B depth) := by
  unfold physicalCoarseSeedLaw
  infer_instance

theorem physicalCoarseSeedLaw_failure (hN : 0 < N)
    (hsize : source.length + target.length ≤ N) (hell : 200 ≤ inputSmallLog N)
    (hB : B = (integerParameters N).B) (hM : M = (integerParameters N).M)
    (hJ : J = intervalTreeDepth M source.length)
    (hdepth : ∀ state, depth state = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi)))
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (physicalCoarseSeedLaw source target N B depth).real
      {seed | ¬ physicalSeedGood source target ((integerParameters N).initialFactor : ℚ) seed} < 1 / 100 := by
  classical
  have hwidth (state : PhysicalEntry M J target.length) :
      coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi) ≤ N := by
    apply max_le
    · exact (physicalSource_length_le source state.1).trans (by omega)
    · have hlen : (substring target state.2.lo state.2.hi).length ≤ target.length := by
        simp only [substring, List.length_drop, List.length_take]
        exact (Nat.sub_le _ _).trans (min_le_right _ _)
      exact hlen.trans (by omega)
  have hcount : Fintype.card (PhysicalEntry M J target.length) ≤ 2 ^ (5 * inputHeight N) := by
    rw [hJ, hM]
    exact computed_labeledEntry_card_le N source.length target.length hN (by omega) (by omega) hell
  have h := computed_fullSeedTable_accuracy N B depth
    (fun state : PhysicalEntry M J target.length => physicalSource source state.1)
    (fun state : PhysicalEntry M J target.length => substring target state.2.lo state.2.hi)
    hB hdepth hN hwidth hcount hell bernstein
  rw [physicalCoarseSeedLaw, map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  have hevents : (physicalCoarseSeedTable source target N B depth) ⁻¹'
      {seed | ¬ physicalSeedGood source target ((integerParameters N).initialFactor : ℚ) seed} =
      {draw : PhysicalCoarseDraw source target B depth | ¬ ∀ state : PhysicalEntry M J target.length,
        stateEditCost (physicalSource source state.1) target state.2 ≤
          coarseFullSeedTable N B depth
            (fun state : PhysicalEntry M J target.length => physicalSource source state.1)
            (fun state : PhysicalEntry M J target.length => substring target state.2.lo state.2.hi) draw state ∧
        coarseFullSeedTable N B depth
            (fun state : PhysicalEntry M J target.length => physicalSource source state.1)
            (fun state : PhysicalEntry M J target.length => substring target state.2.lo state.2.hi) draw state ≤
          (integerParameters N).initialFactor * stateEditCost (physicalSource source state.1) target state.2} := by
    ext draw
    apply not_congr
    unfold physicalSeedGood clampedSeedNat physicalCoarseSeedTable
    constructor
    · intro hg state
      exact ⟨(hg state).1, by exact_mod_cast (hg state).2⟩
    · intro hg state
      exact ⟨(hg state).1, by exact_mod_cast (hg state).2⟩
  rw [hevents]
  exact h

end CoarseLaw

end EditApproximation

end OAI
