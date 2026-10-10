import OAI.Analysis.Hyperinvariant.ProjectionBridge
import OAI.Analysis.FiniteFactor.CrossedProduct.PreparedFactor
import OAI.Analysis.FiniteFactor.CrossedProduct.InvariantProjection
import OAI.Analysis.FiniteFactor.CrossedProduct.HilbertSeparable
import OAI.Analysis.FiniteFactor.Matrix.Entries

namespace OAI

namespace Hyperinvariant
open FiniteFactor MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The fiber indicators form an orthonormal family in the complex Hilbert space. -/
theorem source_basis_orthonormal : Orthonormal ℂ sourceBasis := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [sourceBasis, sourceBasis, sourceFiberIndicator, sourceFiberIndicator,
    L2.inner_indicatorConstLp_one_indicatorConstLp_one
      (hμs := sourceFiberMeasure_ne_top Set.univ i)
      (hμt := sourceFiberMeasure_ne_top Set.univ j)]
  by_cases hij : i = j
  · subst j
    simp [measureReal_def, sourceMeasure, Measure.prod_prod]
  · have he : ((Set.univ : Set (SourceCoordinate → ℝ)) ×ˢ {i}) ∩
        (Set.univ ×ˢ {j}) = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff,
        true_and, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hi hj => hij (hi.symm.trans hj)
    simp [he, hij]

theorem source_infiniteDimensional : ¬FiniteDimensional ℂ (SourceHilbert SourceCoordinate) := by
  intro hfin
  let : FiniteDimensional ℂ (SourceHilbert SourceCoordinate) := hfin
  exact Module.Finite.not_linearIndependent_of_infinite sourceBasis
    source_basis_orthonormal.linearIndependent

/-- The finite-factor construction yields a nonzero norm-quasinilpotent operator
whose ordinary commutant has no nontrivial closed invariant subspace. -/
theorem source_mainClaim : MainClaim (H := SourceHilbert SourceCoordinate) := by
  obtain ⟨θ, hr, hphase, hs, _he, _hcenter, _hfinite, _hminimal, _hpredual,
    hθ, hT, hT0, _hinj, _hcontract, hqn⟩ := exists_source_prepared_factor
  refine ⟨sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg,
    hT0, hqn, ?_⟩
  apply transitiveCommutant_of_invariantProjections (sourceAlgebra θ) _ hT
  intro p hp hproj hinv
  exact sourceInvariantProjection_trivial θ hθ hr hs hphase hp hproj hinv

end
end Hyperinvariant

end OAI
