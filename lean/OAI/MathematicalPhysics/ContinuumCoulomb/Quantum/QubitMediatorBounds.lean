import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorThirdForm

namespace OAI

/-! Applying the third-order estimate to the actual full qubit Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaComplementOperator_norm (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    ‖qmaComplementOperator C D V‖ ≤ ‖qmaPerturbationOperator C D V‖ := by
  let Q := qmaMediatorHighProjection (σ := σ) (κ := κ)
  let P := qmaPerturbationOperator C D V
  have hQ : ‖Q‖ ≤ 1 := qmaMediatorHighProjection_norm
  change ‖Q.comp (P.comp Q)‖ ≤ ‖P‖
  calc
    _ ≤ ‖Q‖*‖P.comp Q‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Q‖*(‖P‖*‖Q‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1*(‖P‖*1) := mul_le_mul hQ
      (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)) (by positivity) zero_le_one
    _ = _ := by ring

theorem qmaComplementOperator_symmetric (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e)
    (x y : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    ⟪x,qmaComplementOperator C D V y⟫_ℝ = ⟪qmaComplementOperator C D V x,y⟫_ℝ := by
  have hQ (u v : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      ⟪u,qmaMediatorHighProjection v⟫_ℝ = ⟪qmaMediatorHighProjection u,v⟫_ℝ :=
    qmaMatrixOperator_real_symmetric _ qmaMediatorHigh_star u v
  have hP (u v : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      ⟪u,qmaPerturbationOperator C D V v⟫_ℝ = ⟪qmaPerturbationOperator C D V u,v⟫_ℝ :=
    qmaMatrixOperator_real_symmetric _ (qmaMediatorPerturbation_star C D V hC hD hV) u v
  change ⟪x,qmaMediatorHighProjection (qmaPerturbationOperator C D V (qmaMediatorHighProjection y))⟫_ℝ =
    ⟪qmaMediatorHighProjection (qmaPerturbationOperator C D V (qmaMediatorHighProjection x)),y⟫_ℝ
  rw [hQ,hP,← hQ]

theorem qmaInverseCoupling_bound (g : ℝ) (hg : 0 < g) (V : κ → Matrix σ σ ℂ)
    {η : ℝ} (hV : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η) (p : EuclideanSpace ℂ σ) :
    ‖qmaPaddedInverse g (qmaCouplingOperator V p)‖ ≤ η*‖p‖ := by
  change ‖qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) p)‖ ≤ _
  rw [qmaPaddedInverse_column,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg)]
  have hnorm : ‖qmaMatrixOperator (qmaAncillaColumn V)‖ ≤ g*η :=
    (qmaAncillaColumn_operator_norm V).trans hV
  have hpoint : ‖qmaMatrixOperator (qmaAncillaColumn V) p‖ ≤
      ‖qmaMatrixOperator (qmaAncillaColumn V)‖*‖p‖ :=
    ContinuousLinearMap.le_opNorm (qmaMatrixOperator (qmaAncillaColumn V)) p
  have hb : ‖qmaMatrixOperator (qmaAncillaColumn V) p‖ ≤ (g*η)*‖p‖ :=
    hpoint.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg p))
  calc
    _ ≤ g⁻¹*((g*η)*‖p‖) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hg.le)
    _ = _ := by field_simp

private theorem extendBlock_lower (a b e μ ε : ℝ)
    (hb : 0 ≤ ε*b) (hl : -ε*a ≤ e-μ*(a+b)) : (μ-ε)*(a+b) ≤ e := by
  nlinarith

theorem qmaPhysical_thirdOrder_lower (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hg : 0 < g) (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) {d m η μ : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hPert : ‖qmaPerturbationOperator C D V‖ ≤ d)
    (hCouple : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η) (hμ : μ ≤ m)
    (hmin : ∀ p : EuclideanSpace ℂ σ,
      μ*‖p‖^2 ≤ qmaQuadratic (qmaThirdMatrix C D V (g:ℂ)) (fun i => p i))
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    (μ-(2*d^2/g+2*m)*η^2)*‖x‖^2 ≤ ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ := by
  have hAT (z : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      qmaPaddedPenalty g (qmaPaddedInverse g z) = z :=
    qmaPaddedPenalty_inverse (σ := σ) (κ := κ) hg z
  have hAsym (z w : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      ⟪z,qmaPaddedPenalty g w⟫_ℝ = ⟪qmaPaddedPenalty g z,w⟫_ℝ :=
    diagonalPenalty_symmetric (qmaPaddedWeight g) z w
  have hgap (z : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
      g*‖z‖^2 ≤ Perturbation.penaltyForm (qmaPaddedPenalty g) z :=
    qmaPaddedPenalty_gap (σ := σ) (κ := κ) hg z
  have hminForm (p : EuclideanSpace ℂ σ) : μ*‖p‖^2 ≤
      Perturbation.thirdOrderForm ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedInverse g) (qmaComplementOperator C D V) (qmaCouplingOperator V) p := by
    rw [qmaActual_thirdOrderForm]
    exact hmin p
  have hl : -(2*d^2/g+2*m)*η^2*‖qmaMediatorRestriction x‖^2 ≤
      Perturbation.lowBlockEnergy ((qmaMatrixOperator C).restrictScalars ℝ)
        (qmaPaddedPenalty g) (qmaComplementOperator C D V) (qmaCouplingOperator V)
        (qmaMediatorRestriction x) (qmaMediatorHighProjection x) -
      μ*(‖qmaMediatorRestriction x‖^2+‖qmaMediatorHighProjection x‖^2) := by
    apply Perturbation.thirdOrder_energy_lower
      ((qmaMatrixOperator C).restrictScalars ℝ) (qmaPaddedPenalty g) (qmaPaddedInverse g)
      (qmaComplementOperator C D V) (qmaCouplingOperator V) hg hd hm hsmall
    · exact hAT
    · exact hAsym
    · exact qmaComplementOperator_symmetric C D V hC hD hV
    · exact hgap
    · exact qmaInverseCoupling_bound g hg V hCouple
    · exact (qmaComplementOperator_norm C D V).trans hPert
    · exact hμ
    · exact hminForm
  have hK : 0 ≤ (2*d^2/g+2*m)*η^2 := by positivity
  have hextra := mul_nonneg hK (sq_nonneg ‖qmaMediatorHighProjection x‖)
  rw [← qmaMediator_norm_decomposition, qmaPhysicalOperator_energy g C D V hC hD hV x]
  apply extendBlock_lower _ _ _ _ _ hextra
  simpa only [neg_mul] using hl

end ContinuumCoulomb

end

end OAI
