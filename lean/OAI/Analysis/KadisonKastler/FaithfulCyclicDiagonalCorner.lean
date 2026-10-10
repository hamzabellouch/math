import OAI.Analysis.KadisonKastler.CountableDiagonalAlgebra
import OAI.Analysis.KadisonKastler.CyclicStandardTracialPosition
import OAI.Analysis.KadisonKastler.SpatialReducingProjection
import OAI.Analysis.KadisonKastler.ReducingCommutantCorner

namespace OAI

/-! # Identifying the standard cyclic corner of the diagonal representation -/

namespace KadisonKastler

noncomputable section

open UnitalTomsWinter Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]

omit [Nontrivial H] in
theorem faithfulCyclic_projection_mem_diagonal_commutant (M : VonNeumannAlgebra H) :
    (faithfulCyclicSpace M).starProjection ∈ (countableDiagonalAlgebra M).commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  obtain ⟨a, rfl⟩ := countableDiagonalHom_surjective M T hT
  exact faithfulCyclic_projection_commutes M a.val a.property

omit [Nontrivial H] in
theorem faithfulCyclic_diagonal_restriction_apply (M : VonNeumannAlgebra H)
    (a : Algebra M) :
    commutantReducingHom (faithfulCyclicSpace M) (countableDiagonalAlgebra M)
      (faithfulCyclic_projection_mem_diagonal_commutant M) (countableDiagonalEquiv M a) =
      faithfulCyclicHom M a := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  rw [commutantReducingHom_apply]
  rw [cornerCompression_coe_of_invariant]
  change l2Diagonal a.val x.val = (faithfulCyclicHom M a x).val
  exact (faithfulCyclicHom_apply M a x).symm
  · intro y hy
    exact invariant_of_commutes_starProjection (faithfulCyclicSpace M)
      (countableDiagonalEquiv M a).val
      (VonNeumannAlgebra.mem_commutant_iff.mp
        (faithfulCyclic_projection_mem_diagonal_commutant M)
        _ (countableDiagonalEquiv M a).property).symm y hy

omit [Nontrivial H] in
theorem faithfulCyclic_diagonal_restriction_range (M : VonNeumannAlgebra H) :
    (commutantReducingHom (faithfulCyclicSpace M) (countableDiagonalAlgebra M)
      (faithfulCyclic_projection_mem_diagonal_commutant M)).range =
      ((faithfulCyclicHom M).range :
        StarSubalgebra ℂ (faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M)) := by
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(countableDiagonalEquiv M).symm a, ?_⟩
    have he := faithfulCyclic_diagonal_restriction_apply M ((countableDiagonalEquiv M).symm a)
    rw [StarAlgEquiv.apply_symm_apply] at he
    exact he.symm
  · rintro ⟨a, rfl⟩
    exact ⟨countableDiagonalEquiv M a, faithfulCyclic_diagonal_restriction_apply M a⟩

omit [Nontrivial H] in
theorem faithfulCyclic_diagonal_corner_eq (M : VonNeumannAlgebra H) :
    generatedVonNeumannAlgebra
      (commutantReducingHom (faithfulCyclicSpace M) (countableDiagonalAlgebra M)
        (faithfulCyclic_projection_mem_diagonal_commutant M)).range =
      faithfulCyclicAlgebra M := by
  rw [faithfulCyclic_diagonal_restriction_range]
  rfl

theorem exists_standardTracialPosition_on_diagonal_corner
    (M : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    Nonempty (StandardTracialPosition (generatedVonNeumannAlgebra
      (commutantReducingHom (faithfulCyclicSpace M) (countableDiagonalAlgebra M)
        (faithfulCyclic_projection_mem_diagonal_commutant M)).range)) := by
  rw [faithfulCyclic_diagonal_corner_eq]
  exact exists_faithfulCyclic_standardTracialPosition M hM

end

end KadisonKastler

end OAI
