import OAI.Analysis.FiniteFactor.CrossedProduct.IndicatorProjection
import OAI.Analysis.FiniteFactor.Diffuse.SmallPartitions
import OAI.Analysis.FiniteFactor.CrossedProduct.Trace
import OAI.Analysis.FiniteFactor.CrossedProduct.VacuumSeparating

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- The original algebra has identity partitions of arbitrarily small trace,
using equal intervals of its first Haar coordinate. -/
theorem sourceAlgebra_small_trace_partitions (θ : SourceCoordinate → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ e : Fin n → (sourceAlgebra θ).toStarSubalgebra,
      (∀ j, IsStarProjection (e j : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)) ∧
      (∑ j, e j) = 1 ∧
      ∀ j, (sourceVacuumFunctional (e j)).re < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1 : ℝ) (1/ε))
  have hnR : (0 : ℝ) < n := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hn)
  have hnN : 0 < n := by exact_mod_cast hnR
  have hsmall : 1/(n : ℝ) < ε := by
    have hh : 1 < (n : ℝ)*ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    exact (div_lt_iff₀ hnR).mpr (by nlinarith)
  let e : Fin n → (sourceAlgebra θ).toStarSubalgebra := fun j =>
    ⟨sourceIndicatorProjection θ (sourceSmallPartitionSet n j) (sourceSmallPartitionSet_measurable n j),
      sourceIndicatorProjection_mem θ _ _⟩
  refine ⟨n,e,fun j => sourceIndicatorProjection_projection θ _ _,?_,?_⟩
  · apply Subtype.ext
    simpa [e] using sourceIndicatorProjection_partition_sum θ n hnN
  · intro j
    change (sourceVacuumFunctional (sourceIndicatorProjection θ (sourceSmallPartitionSet n j)
      (sourceSmallPartitionSet_measurable n j))).re < ε
    rw [sourceIndicatorProjection_trace,Complex.ofReal_re]
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ 1/(n : ℝ))
      (sourceSmallPartitionSet_measure_le n hnN j)).trans_lt hsmall

/-- Actual nonzero proper subprojections of every nonzero projection in the
original algebra. The support construction is internal to this same algebra. -/
theorem sourceAlgebra_hasNoMinimalProjection (θ : SourceCoordinate → ℝ) :
    HasNoMinimalProjection (sourceAlgebra θ) := by
  intro p hp hproj hp0
  let p' : (sourceAlgebra θ).toStarSubalgebra := ⟨p,hp⟩
  obtain ⟨q,hqs,hqi,hq0,hqne,hqp⟩ :=
    Nonhyperlinear.Diffuseness.no_minimal_projection_of_small_partitions
      (sourceAlgebra θ) sourceVacuum
      (fun A B => sourceVacuumFunctional_tracial θ A.property B.property)
      (fun A hz => Subtype.ext (sourceVacuum_separating θ A.property hz))
      (sourceAlgebra_small_trace_partitions θ)
      p' (Subtype.ext hproj.isSelfAdjoint.star_eq) (Subtype.ext hproj.isIdempotentElem)
      (fun hz => hp0 (congrArg Subtype.val hz))
  refine ⟨q,q.property,⟨congrArg Subtype.val hqi,congrArg Subtype.val hqs⟩,?_,?_,congrArg Subtype.val hqp⟩
  · exact fun hz => hq0 (Subtype.ext hz)
  · exact fun hz => hqne (Subtype.ext hz)

end
end FiniteFactor

end OAI
