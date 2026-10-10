import OAI.Analysis.CircleDomains.Sobolev.TensorEnergy

namespace OAI

/-!
# The regularized metric as a matrix

This identifies the scalar energy expression with
`trace ((A + τ I)⁻¹ A) sqrt (det (A + τ I))`, and proves that
regularizing a positive semidefinite tensor gives a positive definite
metric. Thus the energy optimization applies to the actual metric tensor.
-/

open Matrix

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def symmetricTensor (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]

def regularizedTensor (a b c τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricTensor a b c + τ • 1

theorem regularizedTensor_posDef {a b c τ : ℝ}
    (hA : (symmetricTensor a b c).PosSemidef) (hτ : 0 < τ) :
    (regularizedTensor a b c τ).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hτ)

theorem det_regularizedTensor (a b c τ : ℝ) :
    (regularizedTensor a b c τ).det = (a * c - b ^ 2) + τ * (a + c) + τ ^ 2 := by
  simp [regularizedTensor, symmetricTensor, Matrix.det_fin_two]
  ring

theorem det_regularizedTensor_pos {a b c τ : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hD : 0 ≤ a * c - b ^ 2) (hτ : 0 < τ) :
    0 < (regularizedTensor a b c τ).det := by
  rw [det_regularizedTensor]
  exact add_pos_of_nonneg_of_pos (add_nonneg hD (mul_nonneg hτ.le (add_nonneg ha hc)))
    (sq_pos_of_pos hτ)

/-- The actual inverse-matrix energy density equals the scalar invariant
expression used in the dominated-convergence argument. -/
theorem trace_inverse_energy_eq_tensorEnergy {a b c τ : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hD : 0 ≤ a * c - b ^ 2) (hτ : 0 < τ) :
    Matrix.trace ((regularizedTensor a b c τ)⁻¹ * symmetricTensor a b c) *
      Real.sqrt (regularizedTensor a b c τ).det =
      tensorEnergy (a + c) (a * c - b ^ 2) τ := by
  have hpos := det_regularizedTensor_pos ha hc hD hτ
  have hne := ne_of_gt hpos
  have hspos : 0 < Real.sqrt (regularizedTensor a b c τ).det := Real.sqrt_pos.mpr hpos
  have hsq := Real.sq_sqrt hpos.le
  have htrace : Matrix.trace ((regularizedTensor a b c τ)⁻¹ * symmetricTensor a b c) =
      (2 * (a * c - b ^ 2) + τ * (a + c)) / (regularizedTensor a b c τ).det := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
    simp [regularizedTensor, symmetricTensor, Matrix.trace_fin_two, div_eq_mul_inv]
    ring
  rw [htrace, tensorEnergy, ← det_regularizedTensor]
  have hmul := congrArg (fun t : ℝ => (2 * (a * c - b ^ 2) + τ * (a + c)) * t) hsq
  field_simp [hne, hspos.ne']
  nlinarith only [hmul]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
