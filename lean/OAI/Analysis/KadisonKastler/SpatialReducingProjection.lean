import OAI.Analysis.KadisonKastler.CountableOperatorEntries
import OAI.Analysis.KadisonKastler.SpatialSlice
import OAI.Analysis.KadisonKastler.SpatialIsometry
import OAI.Analysis.KadisonKastler.FaithfulCyclicConstruction

namespace OAI

/-! # Reducing projections after tensoring the faithful cyclic representation

The entries of a projection commuting with the countable diagonal algebra
belong to the original commutant. After tensoring, those entries commute
with the whole spatial product, not only its algebraic generators.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Generator.Tracial

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem countableSpatial_commutes
    (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (P : CountableHilbertSum H →L[ℂ] CountableHilbertSum H)
    (hP : ∀ a ∈ M, l2Diagonal a * P = P * l2Diagonal a)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D) :
    l2Diagonal T * (countableTensorEquiv (H := H) (K := K)).conjStarAlgEquiv
        (spatialLeft P) =
      (countableTensorEquiv (H := H) (K := K)).conjStarAlgEquiv
        (spatialLeft P) * l2Diagonal T := by
  apply (countableOperator_commutes_diagonal_iff _ _).mpr
  intro i j
  rw [countableOperatorEntry_spatialLeft]
  have he : countableOperatorEntry P i j ∈ M.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact (countableOperator_commutes_diagonal_iff a P).mp (hP a ha) i j
  exact (spatialLeft_commutes_product M D _ he T hT).symm

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

omit [Nontrivial H] in
theorem faithfulCyclic_projection_commutes (M : VonNeumannAlgebra H)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    l2Diagonal a * (faithfulCyclicSpace M).starProjection =
      (faithfulCyclicSpace M).starProjection * l2Diagonal a := by
  symm
  apply Generator.starProjection_commutes_of_invariant
  · intro x hx
    exact vectorOrbitClosure_invariant (countableDiagonalHom M).range
      (denseSeparatingUnitVector (H := H)) ((countableDiagonalHom M).rangeRestrict ⟨a, ha⟩) hx
  · intro x hx
    change star ((l2DiagonalHom (E := H)) a) x ∈ faithfulCyclicSpace M
    rw [← map_star]
    exact vectorOrbitClosure_invariant (countableDiagonalHom M).range
      (denseSeparatingUnitVector (H := H))
      ((countableDiagonalHom M).rangeRestrict ⟨star a, star_mem ha⟩) hx

omit [Nontrivial H] in
theorem faithfulCyclic_tensor_projection_commutes (M : VonNeumannAlgebra H)
    (D : VonNeumannAlgebra K) (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (hT : T ∈ spatialProductAlgebra M D) :
    l2Diagonal T * (countableTensorEquiv (H := H) (K := K)).conjStarAlgEquiv
        (spatialLeft (faithfulCyclicSpace M).starProjection) =
      (countableTensorEquiv (H := H) (K := K)).conjStarAlgEquiv
        (spatialLeft (faithfulCyclicSpace M).starProjection) * l2Diagonal T :=
  countableSpatial_commutes M D _ (faithfulCyclic_projection_commutes M) T hT

end

end KadisonKastler

end OAI
