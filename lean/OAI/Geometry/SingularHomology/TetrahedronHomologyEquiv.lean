import OAI.Geometry.SingularHomology.TetrahedronHomologyRank

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Problem340.SimplicialSphere

abbrev topCycles := LinearMap.ker (chains.d 2 1).hom

def fundamentalCycleToCycles : ℝ →ₗ[ℝ] topCycles :=
  fundamentalCycle.hom.codRestrict _ (by
    intro r
    change chains.d 2 1 (fundamentalCycle r) = 0
    simpa using ConcreteCategory.congr_hom fundamentalCycle_boundary r)

theorem fundamentalCycleToCycles_leftInverse :
    Function.LeftInverse (fun x : topCycles => coefficient ⟨face 0, face_nondegenerate 0⟩ x.val)
      fundamentalCycleToCycles := by
  intro r
  change coefficient ⟨face 0, face_nondegenerate 0⟩ (fundamentalCycle r) = r
  exact ConcreteCategory.congr_hom fundamentalCycle_coefficient r

theorem firstCycleCoordinate_fundamentalCycleToCycles (r : ℝ) :
    firstCycleCoordinate (fundamentalCycleToCycles r) = r :=
  fundamentalCycleToCycles_leftInverse r

theorem fundamentalCycleToCycles_surjective :
    Function.Surjective fundamentalCycleToCycles := by
  intro x
  refine ⟨firstCycleCoordinate x, ?_⟩
  apply firstCycleCoordinate_injective
  exact firstCycleCoordinate_fundamentalCycleToCycles (firstCycleCoordinate x)

def topCyclesEquivReal : topCycles ≃ₗ[ℝ] ℝ :=
  (LinearEquiv.ofBijective fundamentalCycleToCycles
    ⟨fundamentalCycleToCycles_leftInverse.injective,
      fundamentalCycleToCycles_surjective⟩).symm

theorem normalized_top_boundaries_zero : (chains.sc' 3 2 1).moduleCatToCycles = 0 := by
  ext x
  change chains.d 3 2 x = 0
  rw [incoming_differential_zero]
  rfl

def normalizedHomologyTwoEquivReal :
    (chains.homology 2 : ModuleCat ℝ) ≃ₗ[ℝ] ℝ := by
  have hrange : LinearMap.range (chains.sc' 3 2 1).moduleCatToCycles = ⊥ := by
    rw [normalized_top_boundaries_zero, LinearMap.range_zero]
  exact (chains.homologyIsoSc' 3 2 1 (by simp) (by simp)).toLinearEquiv.trans
    (((chains.sc' 3 2 1).moduleCatHomologyIso.toLinearEquiv.trans
      ((LinearMap.range (chains.sc' 3 2 1).moduleCatToCycles).quotEquivOfEqBot hrange)).trans
        topCyclesEquivReal)

def homologyTwoEquivReal : (sphere.homology coefficients 2 : ModuleCat ℝ) ≃ₗ[ℝ] ℝ :=
  (asIso (HomologicalComplex.homologyMap
    (sphere.toNormalizedChainComplex coefficients) 2)).toLinearEquiv.trans
      normalizedHomologyTwoEquivReal

end Problem340.SimplicialSphere

end

end OAI
