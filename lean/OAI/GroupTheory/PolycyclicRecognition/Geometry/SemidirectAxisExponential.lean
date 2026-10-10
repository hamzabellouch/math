import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import OAI.GroupTheory.PolycyclicRecognition.Analysis.OneParameterIntegralCurve

namespace OAI

/-! # Exponential curves along the two factors of the semidirect product -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem semidirect_exp_left_axis (x : L) (t : ℝ) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    groupExponential (G := L × ℝ) (t • ((x, 0) : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ))) =
      (t • x, 0) := by
  let _ : Group (L × ℝ) := derivationSemidirectGroup D hD
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let := derivationSemidirectLieGroup D hD
  let v : L × ℝ := (x, 0)
  have hzero : (0 : ℝ) • v = (1 : L × ℝ) := by
    rw [zero_smul]
    exact (derivationSemidirect_one D hD).symm
  have hmul (s u : ℝ) : (s + u) • v = (s • v) * (u • v) := by
    change (s + u) • v = (derivationSemidirectGroup D hD).mul (s • v) (u • v)
    rw [derivationSemidirect_mul]
    simp only [v, Prod.smul_mk, smul_zero, nilpotentDerivationFlow_zero,
      PolynomialExponentialCoordinates.smul_mul, zero_add]
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const v).hasMFDerivAt
  have h := oneParameter_eq_groupExponential groupExponential_isGroupExponential hzero hmul v hd t
  have hv : t • v = (t • x, 0) := by simp [v]
  exact h.symm.trans hv

theorem semidirect_exp_right_axis (t : ℝ) :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    groupExponential (G := L × ℝ) (t • ((0, 1) : GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ))) =
      (0, t) := by
  let _ : Group (L × ℝ) := derivationSemidirectGroup D hD
  let _ : Mul (L × ℝ) := (derivationSemidirectGroup D hD).toMul
  let _ : One (L × ℝ) := (derivationSemidirectGroup D hD).toOne
  let := derivationSemidirectLieGroup D hD
  let v : L × ℝ := (0, 1)
  have hzero : (0 : ℝ) • v = (1 : L × ℝ) := by
    rw [zero_smul]
    exact (derivationSemidirect_one D hD).symm
  have hmul (s u : ℝ) : (s + u) • v = (s • v) * (u • v) := by
    change ((s + u) • (0 : L), (s + u) * 1) =
      (s • (0 : L) * nilpotentDerivationFlow D hD (s * 1) (u • (0 : L)), s * 1 + u * 1)
    simp only [smul_zero, mul_one, map_zero]
    rw [← P.one_eq_zero, mul_one]
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const v).hasMFDerivAt
  have h := oneParameter_eq_groupExponential groupExponential_isGroupExponential hzero hmul v hd t
  have hv : t • v = (0, t) := by simp [v]
  exact h.symm.trans hv

end PolycyclicRecognition

end

end OAI
