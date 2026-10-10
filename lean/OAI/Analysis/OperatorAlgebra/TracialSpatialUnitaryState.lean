import OAI.Analysis.OperatorAlgebra.TracialProductApproximation
import OAI.Analysis.Nuclearity.SpatialStateUltralimit

namespace OAI

/-! The spatial diagonal state in the finite tracial injectivity argument.
The finite-vector argument follows Anantharaman--Delaroche,
Pacific J. Math. 171 (1995), Lemma 3.7 and Proposition 3.6, pp. 328--330. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem expectation_tracial_spatial_unitary_state (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T) :
    ∃ φ : (NuclearUltrapower.HilbertSchmidt H →L[ℂ]
        NuclearUltrapower.HilbertSchmidt H) →ₚ[ℂ] ℂ,
      φ 1 = 1 ∧ ∀ (a : M.toStarSubalgebra) (u : unitary M.toStarSubalgebra),
        φ (densityLeftRepresentation (a : H →L[ℂ] H) *
          densityRightRepresentation (MulOpposite.op ((u : M.toStarSubalgebra) : H →L[ℂ] H))) =
            τ.functional (a * (u : M.toStarSubalgebra)) := by
  classical
  let T (p : M.toStarSubalgebra × unitary M.toStarSubalgebra) :=
    densityLeftRepresentation (p.1 : H →L[ℂ] H) *
      densityRightRepresentation
        (MulOpposite.op ((p.2 : M.toStarSubalgebra) : H →L[ℂ] H))
  let c (p : M.toStarSubalgebra × unitary M.toStarSubalgebra) :=
    τ.functional (p.1 * (p.2 : M.toStarSubalgebra))
  have happrox (s : Finset (M.toStarSubalgebra × unitary M.toStarSubalgebra))
      (ε : ℝ) (hε : 0 < ε) :
      ∃ ξ : NuclearUltrapower.HilbertSchmidt H, ‖ξ‖ = 1 ∧
        ∀ p ∈ s, ‖inner ℂ ξ (T p ξ) - c p‖ < ε := by
    obtain ⟨ξ, hξ, _, _, htest⟩ := expectation_spatial_product_approximation
      M τ E hE hEr hEf (fun p : s => p.val.1) (fun p : s => p.val.2) hε
    refine ⟨ξ, hξ, ?_⟩
    intro p hp
    exact htest ⟨p, hp⟩
  obtain ⟨φ, hφ, hprod⟩ := exists_spatial_state_of_finite_approximation T c happrox
  exact ⟨φ, hφ, fun a u => hprod (a, u)⟩

end WeakPureInfiniteness

end

end OAI
