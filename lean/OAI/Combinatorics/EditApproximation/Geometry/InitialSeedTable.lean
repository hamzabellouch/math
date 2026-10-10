import OAI.Combinatorics.EditApproximation.Coarse.CoarseGlobalSeed
import OAI.Combinatorics.EditApproximation.Geometry.StateDomain

namespace OAI

/-!
# Simultaneous initial accuracy on the actual labeled state domain

The source and target arguments are the stored substrings at each physical
node and valid target interval. The entry-size and whole-domain cardinal
premises of the coarse seed theorem are discharged here.
-/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem initialSeedTable_width_bound {α : Type*} (N M : ℕ) (source target : List α)
    (hsize : source.length + target.length ≤ N)
    (entry : LabeledEntry M source.length target.length) :
    coarseEntryWidth (entrySource M source entry) (entryTarget target entry) ≤ N := by
  apply max_le
  · exact (entrySource_length_le M source entry).trans (by omega)
  · exact (entryTarget_length_le target entry).trans (by omega)

theorem initialSeedTable_accuracy {α : Type*} [DecidableEq α]
    (N B M : ℕ) [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
    (source target : List α)
    (depth : LabeledEntry M source.length target.length → ℕ)
    (hB : B = (integerParameters N).B) (hM : M = (integerParameters N).M)
    (hdepth : ∀ entry, depth entry = computedCoarseDepth N
      (coarseEntryWidth (entrySource M source entry) (entryTarget target entry)))
    (hN : 0 < N) (hsize : source.length + target.length ≤ N)
    (hell : 200 ≤ inputSmallLog N)
    (bernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure)) :
    (coarseFullSeedMeasure B depth (entrySource M source) (entryTarget target)).real
      {draws | ¬ ∀ entry : LabeledEntry M source.length target.length,
        stateEditCost (entrySource M source entry) target entry.2 ≤
          coarseFullSeedTable N B depth (entrySource M source) (entryTarget target) draws entry ∧
        coarseFullSeedTable N B depth (entrySource M source) (entryTarget target) draws entry ≤
          (integerParameters N).initialFactor *
            stateEditCost (entrySource M source entry) target entry.2} < 1 / 100 := by
  have hcount : Fintype.card (LabeledEntry M source.length target.length) ≤
      2 ^ (5 * inputHeight N) := by
    rw [hM]
    exact computed_labeledEntry_card_le N source.length target.length hN (by omega) (by omega) hell
  exact computed_fullSeedTable_accuracy N B depth (entrySource M source) (entryTarget target)
    hB hdepth hN (initialSeedTable_width_bound N M source target hsize) hcount hell bernstein

end EditApproximation

end OAI
