import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorBounds

namespace OAI

/-! The third-order trial vector lies in the genuine physical spin space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaThirdTrial (g : ℝ) (V : κ → Matrix σ σ ℂ) (p : EuclideanSpace ℂ σ) :
    EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  qmaMediatorInclusion p+(-(qmaPaddedInverse g (qmaCouplingOperator V p)))

theorem qmaThirdTrial_high_kernel (g : ℝ) (V : κ → Matrix σ σ ℂ) (p : EuclideanSpace ℂ σ) :
    qmaMediatorRestriction (-(qmaPaddedInverse g (qmaCouplingOperator V p))) = 0 := by
  change qmaMediatorRestriction (-(qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p))) = 0
  rw [qmaPaddedInverse_column,map_neg,map_smul,qmaMediatorRestriction_column,smul_zero,neg_zero]

theorem qmaThirdTrial_norm (g : ℝ) (V : κ → Matrix σ σ ℂ) (p : EuclideanSpace ℂ σ) :
    ‖qmaThirdTrial g V p‖^2 = ‖p‖^2+‖qmaPaddedInverse g (qmaCouplingOperator V p)‖^2 := by
  have h := Perturbation.orthogonalAssemble_norm
    (qmaMediatorInclusion (σ := σ) (κ := κ)) (qmaMediatorRestriction (σ := σ) (κ := κ))
    qmaMediator_restrict_include qmaMediator_inclusion_adjoint p
    (-(qmaPaddedInverse g (qmaCouplingOperator V p))) (qmaThirdTrial_high_kernel g V p)
  simpa only [qmaThirdTrial,norm_neg] using h

theorem qmaThirdTrial_energy (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) (p : EuclideanSpace ℂ σ) :
    ⟪qmaThirdTrial g V p,qmaPhysicalOperator g C D V (qmaThirdTrial g V p)⟫_ℝ =
      Perturbation.lowBlockEnergy ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedPenalty g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p
        (-(qmaPaddedInverse g (qmaCouplingOperator V p))) := by
  exact Perturbation.orthogonalBlock_energy
    (qmaMediatorInclusion (σ := σ) (κ := κ)) (qmaMediatorRestriction (σ := σ) (κ := κ))
    (qmaPhysicalOperator g C D V) (qmaPaddedPenalty g) (qmaComplementOperator C D V)
    ((qmaMatrixOperator C).restrictScalars ℝ) (qmaCouplingOperator V)
    qmaMediator_restrict_include qmaMediator_inclusion_adjoint
    (qmaMatrixOperator_real_symmetric _ (qmaPhysicalMediator_star g C D V hC hD hV))
    (qmaPhysicalOperator_low g C D V) (qmaMediatorRestriction_column V)
    (qmaPhysicalOperator_high g C D V) p _ (qmaThirdTrial_high_kernel g V p)

theorem qmaPhysical_thirdOrder_trial (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hg : 0 < g) (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) {m η μ : ℝ} (hm : 0 ≤ m)
    (hCouple : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η) (hμ : -m ≤ μ)
    (p : EuclideanSpace ℂ σ) (hp : ‖p‖ = 1)
    (he : qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i) = μ) :
    0 < ‖qmaThirdTrial g V p‖^2 ∧
      ⟪qmaThirdTrial g V p,qmaPhysicalOperator g C D V (qmaThirdTrial g V p)⟫_ℝ /
        ‖qmaThirdTrial g V p‖^2 ≤ μ+m*η^2 := by
  constructor
  · rw [qmaThirdTrial_norm,hp]
    positivity
  · rw [qmaThirdTrial_energy g C D V hC hD hV,qmaThirdTrial_norm]
    have hAT (z : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
        qmaPaddedPenalty g (qmaPaddedInverse g z) = z :=
      qmaPaddedPenalty_inverse (σ := σ) (κ := κ) hg z
    have heForm : Perturbation.thirdOrderForm ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p = μ := by
      rw [qmaActual_thirdOrderForm]
      exact he
    have h : Perturbation.lowBlockRayleigh ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedPenalty g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p
        (-(qmaPaddedInverse g (qmaCouplingOperator V p))) ≤ μ+m*η^2 := by
      apply Perturbation.thirdOrder_trial_upper ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedPenalty g) (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V) hm
      · exact hAT
      · exact qmaInverseCoupling_bound g hg V hCouple
      · exact hμ
      · exact hp
      · exact heForm
    simpa only [Perturbation.lowBlockRayleigh,norm_neg] using h

end ContinuumCoulomb

end

end OAI
