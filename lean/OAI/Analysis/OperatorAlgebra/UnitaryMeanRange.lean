import OAI.Analysis.OperatorAlgebra.UnitaryMeanCP
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

/-! Averaging stays in a von Neumann algebra whenever each conjugate does.
This uses the actual double-commutant condition on matrix coefficients. -/

noncomputable section
open Filter
open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def orbitConjugate (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap * T *
    U.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace H] in
lemma orbitConjugate_inner (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) (x y : H) :
    inner ℂ (orbitConjugate U T x) y = inner ℂ (T (U x)) (U y) := by
  change inner ℂ (U.symm (T (U x))) y = _
  rw [U.symm.inner_map_eq_flip]
  rfl

theorem unitaryOrbitMean_mem (ω : Ultrafilter ℕ)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hU : ∀ x, Continuous (fun t => U t x))
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (hT : ∀ t, orbitConjugate (U t) T ∈ M) :
    unitaryOrbitMean ω U hU T ∈ M := by
  rw [← M.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro R hR
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (R (unitaryOrbitMean ω U hU T x)) y =
    inner ℂ (unitaryOrbitMean ω U hU T (R x)) y
  rw [← ContinuousLinearMap.adjoint_inner_right, unitaryOrbitMean_inner,
    unitaryOrbitMean_inner]
  apply congrArg (complexSymmetricMean ω)
  ext t
  change inner ℂ (T (U t x)) (U t (R.adjoint y)) =
    inner ℂ (T (U t (R x))) (U t y)
  rw [← orbitConjugate_inner, ← orbitConjugate_inner,
    ContinuousLinearMap.adjoint_inner_right]
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp hR _ (hT t)
  exact congrArg (fun A : H →L[ℂ] H => inner ℂ (A x) y) hc.symm

end WeakPureInfiniteness

end

end OAI
