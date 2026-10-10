import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace Kadison

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_unitary_compact : IsCompact (unitary (Matrix ι ι ℂ) : Set (Matrix ι ι ℂ)) := by
  have hb : Bornology.IsBounded (unitary (Matrix ι ι ℂ) : Set (Matrix ι ι ℂ)) := by
    apply (Metric.isBounded_closedBall (x := (0 : Matrix ι ι ℂ)) (r := 1)).subset
    intro a ha
    rw [Metric.mem_closedBall,dist_zero_right]
    by_cases hι : Nonempty ι
    · let _ := hι
      exact (CStarRing.norm_coe_unitary (⟨a,ha⟩ : unitary (Matrix ι ι ℂ))).le
    · have : IsEmpty ι := not_nonempty_iff.mp hι
      have h : a=0 := Subsingleton.elim _ _
      rw [h,norm_zero]
      exact zero_le_one
  exact Metric.isCompact_of_isClosed_isBounded isClosed_unitary hb

instance matrixUnitaryCompactSpace : CompactSpace (unitary (Matrix ι ι ℂ)) :=
  isCompact_iff_compactSpace.mp matrix_unitary_compact

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

def compactHaarProbability : Measure G :=
  haarMeasure (⟨⟨Set.univ,isCompact_univ⟩,by simp⟩ : PositiveCompacts G)

instance compactHaarProbability_isProbability : IsProbabilityMeasure (compactHaarProbability G) where
  measure_univ := haarMeasure_self

instance compactHaarProbability_isLeftInvariant : IsMulLeftInvariant (compactHaarProbability G) :=
  inferInstanceAs (IsMulLeftInvariant (haarMeasure _))

end Kadison

end

end
end

end OAI
