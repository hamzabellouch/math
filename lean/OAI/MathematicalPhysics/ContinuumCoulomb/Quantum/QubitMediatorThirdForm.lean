import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorForms
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorSeriesError
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOperatorQuadratic

namespace OAI

/-! The actual third-order Hilbert form is the computed finite matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq σ] in
theorem qmaThirdMatrix_compressed (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    qmaThirdMatrix C D V (g:ℂ) =
      C-(g⁻¹:ℝ) • ((qmaAncillaColumn V).conjTranspose*qmaAncillaColumn V)+
        (g⁻¹^2:ℝ) • ((qmaAncillaColumn V).conjTranspose*
          qmaMediatorPerturbation C D V*qmaAncillaColumn V) := by
  have hs (s : ℝ) (M : Matrix σ σ ℂ) : s • M = (s:ℂ) • M := rfl
  simp only [hs,Complex.ofReal_pow,Complex.ofReal_inv,qmaThirdMatrix,
    qmaAncillaColumn_gram,qmaMediatorPerturbation_compression]

theorem qmaActual_thirdOrderForm (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (p : EuclideanSpace ℂ σ) :
    Perturbation.thirdOrderForm ((qmaMatrixOperator C).restrictScalars ℝ)
      (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p =
        qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i) := by
  have hgram : qmaQuadratic ((qmaAncillaColumn V).conjTranspose*qmaAncillaColumn V)
      (fun i => p i) = ⟪qmaMatrixOperator (qmaAncillaColumn V) p,
        qmaMatrixOperator (qmaAncillaColumn V) p⟫_ℝ := by
    have h := qmaQuadratic_sandwich (qmaAncillaColumn V)
      (1 : Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ) p
    simpa only [Matrix.mul_one,qmaMatrixOperator_square,spinMatrixOperator_one,
      one_apply_eq_self] using h
  have hcompress := qmaQuadratic_sandwich (qmaAncillaColumn V) (qmaMediatorPerturbation C D V) p
  rw [qmaThirdMatrix_compressed,qmaQuadratic_add,qmaQuadratic_sub,qmaQuadratic_real_smul,
    qmaQuadratic_real_smul,qmaQuadratic_operator C p,hgram,hcompress]
  unfold Perturbation.thirdOrderForm Perturbation.effectiveForm Perturbation.inverseForm
  change ⟪p,qmaMatrixOperator C p⟫_ℝ-
    ⟪qmaMatrixOperator (qmaAncillaColumn V) p,qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p)⟫_ℝ+
    ⟪qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p),
      qmaComplementOperator C D V (qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p))⟫_ℝ = _
  rw [qmaPaddedInverse_column]
  simp only [map_smul,real_inner_smul_left,real_inner_smul_right]
  rw [qmaComplementOperator_form C D V _ (qmaMediatorRestriction_column V p)]
  have he : qmaPerturbationOperator C D V (qmaMatrixOperator (qmaAncillaColumn V) p) =
      qmaMatrixOperator (qmaMediatorPerturbation C D V) (qmaMatrixOperator (qmaAncillaColumn V) p) := rfl
  rw [he]
  ring

end ContinuumCoulomb

end

end OAI
