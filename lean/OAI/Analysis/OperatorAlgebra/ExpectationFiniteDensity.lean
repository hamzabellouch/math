import OAI.Analysis.OperatorAlgebra.HypertraceFiniteDensity
import OAI.Analysis.OperatorAlgebra.ExpectationHypertrace

namespace OAI

/-! The constructed conditional expectation supplies the finite hypertrace
witness. All conjugations below are the actual unitaries of the represented
algebra, and the errors are measured in the norm of vector functionals. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {H I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def subalgebraUnitaryIsometry (M : StarSubalgebra ℂ (H →L[ℂ] H)) (u : unitary M) : H ≃ₗᵢ[ℂ] H :=
  Unitary.linearIsometryEquiv (Unitary.map (StarMonoidHom.ofClass M.subtype) u)

lemma conjugatedOperator_subalgebraUnitary (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (u : unitary M) (T : H →L[ℂ] H) :
    conjugatedOperator (subalgebraUnitaryIsometry M u) T =
      star ((u : M) : H →L[ℂ] H) * T * ((u : M) : H →L[ℂ] H) := by
  ext x
  rfl

lemma hypertrace_subalgebraUnitary_invariant (M : StarSubalgebra ℂ (H →L[ℂ] H))
    (φ : (H →L[ℂ] H) →ₚ[ℂ] ℂ)
    (hc : ∀ (a : M) (T : H →L[ℂ] H), φ ((a : H →L[ℂ] H) * T) = φ (T * (a : H →L[ℂ] H)))
    (u : unitary M) (T : H →L[ℂ] H) :
    φ (conjugatedOperator (subalgebraUnitaryIsometry M u) T) = φ T := by
  let v := Unitary.map (StarMonoidHom.ofClass M.subtype) u
  rw [conjugatedOperator_subalgebraUnitary]
  change φ (star (v : H →L[ℂ] H) * T * (v : H →L[ℂ] H)) = φ T
  rw [mul_assoc]
  have hh := hc (star (u : M)) (T * (v : H →L[ℂ] H))
  change φ (star (v : H →L[ℂ] H) * (T * (v : H →L[ℂ] H))) =
    φ ((T * (v : H →L[ℂ] H)) * star (v : H →L[ℂ] H)) at hh
  rw [hh, mul_assoc, Unitary.mul_star_self_of_mem v.property, mul_one]

variable [Fintype I] [Fintype J]

/-- Finite normal positive approximations with norm-small unitary defects,
obtained from the actual expectation and a tracial state. -/
theorem expectation_finite_density (M : VonNeumannAlgebra H)
    [PartialOrder M.toStarSubalgebra] [StarOrderedRing M.toStarSubalgebra]
    (τ : Pureness.TracialState M.toStarSubalgebra)
    (E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H))
    (hE : CompletelyPositive E) (hEr : ∀ T, E T ∈ M)
    (hEf : ∀ T, T ∈ M → E T = T)
    (a : I → selfAdjoint M.toStarSubalgebra) (u : J → unitary M.toStarSubalgebra)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (x : Fin n → H),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧ (∀ k, ‖x k‖ ≤ 1) ∧
      (∀ i, |(τ.functional (a i)).re -
        ∑ k, w k * (inner ℂ (x k) (((a i : M.toStarSubalgebra) : H →L[ℂ] H) (x k))).re| < ε) ∧
      ∀ j, ‖finitePredualUnitary (subalgebraUnitaryIsometry M.toStarSubalgebra (u j))
        (finiteVectorDensity w x) - finiteVectorDensity w x‖ < ε := by
  obtain ⟨φ, hφ, hφa, hc⟩ := expectation_hypertrace M τ E hE hEr hEf
  have ha (i : I) : IsSelfAdjoint ((a i : M.toStarSubalgebra) : H →L[ℂ] H) :=
    (a i).property.map M.toStarSubalgebra.subtype
  have hu (j : J) (T : H →L[ℂ] H) :
      φ (conjugatedOperator (subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) T) = φ T :=
    hypertrace_subalgebraUnitary_invariant M.toStarSubalgebra φ hc (u j) T
  simpa only [hφa] using hypertrace_finite_density
    (fun i => ((a i : M.toStarSubalgebra) : H →L[ℂ] H)) ha
    (fun j => subalgebraUnitaryIsometry M.toStarSubalgebra (u j)) φ hφ hu hε

end WeakPureInfiniteness

end

end OAI
