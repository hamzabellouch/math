import OAI.Analysis.KadisonSimilarity.Representation.Amplification
import Mathlib.Basic.ENNReal.Real

namespace OAI

/-! The Arveson commutant-distance formula reduces hyperreflexivity to
uniform matrix commutator bounds and the scalar spectral estimate.
The formula is recorded in Christensen, Sinclair, Smith and White,
*Perturbations of C*-algebraic invariants*, Geom. Funct. Anal. 20 (2010),
368–397, Equation (2.1). -/

noncomputable section

namespace KadisonSimilarity

universe u

open scoped ENNReal

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Completely bounded norm of the inner derivation restricted to `P`.
The extended nonnegative real value permits this norm to be infinite before
an estimate has been proved. Matrix norms are the concrete Hilbert norms. -/
def completeCommutatorNorm (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H))
    (_ : ∀ i j, X i j ∈ P) (_ : ‖matrixOperator X‖ ≤ 1),
    ENNReal.ofReal ‖commutator (amplify Y n) (matrixOperator X)‖

/-- The specialization of CSSW (2010), Equation (2.1), used for this operator.
`M` is already equal to its double commutant by its `VonNeumannAlgebra` structure. -/
def ArvesonDistanceFormula (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) : Prop :=
  completeCommutatorNorm M.commutant T =
    ENNReal.ofReal (2 * Metric.infDist T (M : Set (H →L[ℂ] H)))

/-- A uniform concrete matrix estimate controls the completely bounded norm. -/
theorem completeCommutatorNorm_le (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (estimate : CommutatorEstimate P C) :
    completeCommutatorNorm P Y ≤ ENNReal.ofReal (C * scalarCommutatorNorm P Y) := by
  refine iSup_le fun n => iSup_le fun X => iSup_le fun hXP => iSup_le fun hX => ?_
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖commutator (amplify Y n) (matrixOperator X)‖ ≤
        C * scalarCommutatorNorm P Y * ‖matrixOperator X‖ := estimate Y n X hXP
    _ ≤ C * scalarCommutatorNorm P Y :=
      mul_le_of_le_one_right (mul_nonneg hC (scalarCommutatorNorm_nonneg P Y)) hX

/-- Application of the published distance formula. This deduction contains no
additional analytic hypothesis beyond the stated matrix estimate. -/
theorem twice_distance_le_of_arveson (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (arveson : ArvesonDistanceFormula M T)
    (estimate : CommutatorEstimate M.commutant C) :
    2 * Metric.infDist T (M : Set (H →L[ℂ] H)) ≤
      C * scalarCommutatorNorm M.commutant T := by
  have h := completeCommutatorNorm_le M.commutant T hC estimate
  rw [arveson] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (scalarCommutatorNorm_nonneg M.commutant T))).mp h

/-- The quantitative hyperreflexivity bound from the commutant-distance
formula, a uniform matrix estimate, and the scalar spectral bound. -/
theorem hyperreflexivity_bound_of_arveson (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (arveson : ArvesonDistanceFormula M T)
    (estimate : CommutatorEstimate M.commutant C)
    (scalarBound : scalarCommutatorNorm M.commutant T ≤ 4 * offDiagonalSeminorm M T) :
    Metric.infDist T (M : Set (H →L[ℂ] H)) ≤ 2 * C * offDiagonalSeminorm M T := by
  have h := twice_distance_le_of_arveson M T hC arveson estimate
  have h' := mul_le_mul_of_nonneg_left scalarBound hC
  nlinarith

end KadisonSimilarity

end

end OAI
