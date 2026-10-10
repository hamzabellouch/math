import OAI.Analysis.OperatorAlgebra.TracialSpatialUnitaryState
import OAI.Analysis.PureInfiniteness.UnitarySpanEquality

namespace OAI

/-! The spatial diagonal state in the finite tracial injectivity argument.
The finite-vector argument follows Anantharaman--Delaroche,
Pacific J. Math. 171 (1995), Lemma 3.7 and Proposition 3.6, pp. 328--330. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma tracial_spatial_state_extend (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (φ : (NuclearUltrapower.HilbertSchmidt H →L[ℂ]
      NuclearUltrapower.HilbertSchmidt H) →ₚ[ℂ] ℂ)
    (hprod : ∀ (a : M.toStarSubalgebra) (u : unitary M.toStarSubalgebra),
      φ (densityLeftRepresentation (a : H →L[ℂ] H) *
        densityRightRepresentation (MulOpposite.op ((u : M.toStarSubalgebra) : H →L[ℂ] H))) =
          τ.functional (a * (u : M.toStarSubalgebra))) (a b : M.toStarSubalgebra) :
    φ (densityLeftRepresentation (a : H →L[ℂ] H) *
      densityRightRepresentation (MulOpposite.op (b : H →L[ℂ] H))) =
        τ.functional (a * b) := by
  let L := densityLeftRepresentation (H := H) (a : H →L[ℂ] H)
  let ρ : M.toStarSubalgebra →ₗ[ℂ]
      (NuclearUltrapower.HilbertSchmidt H →L[ℂ] NuclearUltrapower.HilbertSchmidt H) :=
    (densityRightRepresentation (H := H)).toLinearMap.comp
      ((MulOpposite.opLinearEquiv ℂ (M := H →L[ℂ] H)).toLinearMap.comp
        M.toStarSubalgebra.subtype.toLinearMap)
  let f : M.toStarSubalgebra →ₗ[ℂ] ℂ :=
    φ.toLinearMap.comp ((LinearMap.mulLeft ℂ L).comp ρ)
  let g : M.toStarSubalgebra →ₗ[ℂ] ℂ :=
    τ.functional.toLinearMap.comp (LinearMap.mulLeft ℂ a)
  have hunit : ∀ u : unitary M.toStarSubalgebra, f u = g u := fun u => hprod a u
  exact congrArg (fun k : M.toStarSubalgebra →ₗ[ℂ] ℂ => k b)
    (linearMap_ext_unitaries f g hunit)

/-- The trace diagonal is realized by an actual spatial state. -/
theorem expectation_tracial_spatial_state (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T) :
    ∃ φ : (NuclearUltrapower.HilbertSchmidt H →L[ℂ]
        NuclearUltrapower.HilbertSchmidt H) →ₚ[ℂ] ℂ,
      φ 1 = 1 ∧ ∀ a b : M.toStarSubalgebra,
        φ (densityLeftRepresentation (a : H →L[ℂ] H) *
          densityRightRepresentation (MulOpposite.op (b : H →L[ℂ] H))) =
            τ.functional (a * b) := by
  obtain ⟨φ, hφ, hprod⟩ := expectation_tracial_spatial_unitary_state M τ E hE hEr hEf
  exact ⟨φ, hφ, tracial_spatial_state_extend M τ φ hprod⟩

end WeakPureInfiniteness

end

end OAI
