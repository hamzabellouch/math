import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace Kadison.UnitaryHaar

variable (A : Type*) [CStarAlgebra A] [FiniteDimensional ℂ A] [Nontrivial A]

abbrev compactUnitary : CompactSpace (unitary A) := by
  let : ProperSpace A := FiniteDimensional.proper ℂ A
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0:A) 1).of_isClosed_subset isClosed_unitary
  intro a ha
  simp only [Metric.mem_closedBall,dist_zero_right]
  exact (CStarRing.norm_of_mem_unitary ha).le

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

def whole : PositiveCompacts G where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

def probability : Measure G := haarMeasure (whole G)

instance : IsProbabilityMeasure (probability G) where
  measure_univ := haarMeasure_self

instance : IsMulLeftInvariant (probability G) := by
  dsimp only [probability]
  infer_instance

end Kadison.UnitaryHaar

end

end
end

end OAI
