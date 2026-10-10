import OAI.AlgebraicGeometry.StableCoordinate.Definitions
import Mathlib.Algebra.MvPolynomial.Equiv

namespace OAI

/-!
# The added variable is a genuine polynomial indeterminate

The target encodes `R[w]` as a polynomial algebra on five independent
variables. Here that encoding is identified with the literal univariate
polynomial ring over `R 4`, fixing all original variables. Conjugating
algebra automorphisms through this equivalence shows that the target's
stabilization criterion is exactly the one in the source, with no
condition that the automorphism preserve the coefficient subring.
-/

namespace StableCoordinate

open MvPolynomial

/-- The last of five independent variables becomes the new indeterminate;
the first four become coefficient variables. -/
noncomputable def stabilizationEquiv : R 5 ≃ₐ[ℂ] Polynomial (R 4) :=
  (renameEquiv ℂ (finSuccEquivLast : Fin 5 ≃ Option (Fin 4))).trans
    (optionEquivLeft ℂ (Fin 4))

@[simp]
theorem stabilizationEquiv_X_castSucc (i : Fin 4) :
    stabilizationEquiv (X i.castSucc) = Polynomial.C (X i) := by
  simp [stabilizationEquiv, renameEquiv_apply]

@[simp]
theorem stabilizationEquiv_X_last :
    stabilizationEquiv (X 4) = Polynomial.X := by
  have h : (finSuccEquivLast : Fin 5 ≃ Option (Fin 4)) (4 : Fin 5) = none :=
    finSuccEquivLast_last
  simp [stabilizationEquiv, renameEquiv_apply, h]

@[simp]
theorem stabilizationEquiv_stabilize (g : R 4) :
    stabilizationEquiv (stabilize g) = Polynomial.C g := by
  have h : stabilizationEquiv.toAlgHom.comp stabilize =
      (Polynomial.CAlgHom : R 4 →ₐ[ℂ] Polynomial (R 4)) := by
    ext i
    simp [stabilize]
  exact AlgHom.congr_fun h g

@[simp]
theorem stabilizationEquiv_symm_C (g : R 4) :
    stabilizationEquiv.symm (Polynomial.C g) = stabilize g := by
  apply stabilizationEquiv.injective
  simp

/-- Adjoining the variable does not identify distinct original polynomials. -/
theorem stabilize_injective : Function.Injective stabilize := by
  intro g h hgh
  apply Polynomial.C_injective
  simpa using congrArg stabilizationEquiv hgh

/-- The added variable is not already in the original four-variable subring. -/
theorem last_variable_not_mem_stabilize_range :
    (X 4 : R 5) ∉ Set.range stabilize := by
  rintro ⟨g, hg⟩
  have h := congrArg stabilizationEquiv hg
  simp only [stabilizationEquiv_stabilize, stabilizationEquiv_X_last] at h
  exact Polynomial.X_ne_C g h.symm

/-- Exact compatibility between the five-variable encoding and the literal
`R[w]` automorphism criterion. Both automorphisms are arbitrary complex
algebra automorphisms, not coefficient-algebra automorphisms. -/
theorem isOneStableCoordinate_iff_polynomial (g : R 4) :
    IsOneStableCoordinate g ↔
      ∃ φ : Polynomial (R 4) ≃ₐ[ℂ] Polynomial (R 4),
        φ (Polynomial.C g) = Polynomial.C (X 0) := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨stabilizationEquiv.symm.trans (φ.trans stabilizationEquiv), ?_⟩
    change stabilizationEquiv (φ (stabilizationEquiv.symm (Polynomial.C g))) = _
    rw [stabilizationEquiv_symm_C, hφ]
    exact stabilizationEquiv_X_castSucc 0
  · rintro ⟨φ, hφ⟩
    refine ⟨stabilizationEquiv.trans (φ.trans stabilizationEquiv.symm), ?_⟩
    change stabilizationEquiv.symm (φ (stabilizationEquiv (stabilize g))) = _
    rw [stabilizationEquiv_stabilize, hφ, stabilizationEquiv_symm_C]
    simp [stabilize]

end StableCoordinate

end OAI
