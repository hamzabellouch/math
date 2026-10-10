import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorPhysical

namespace OAI

/-! The full physical energy equals the block energy on its genuine
vacuum/complement decomposition. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

omit [DecidableEq σ] in
theorem qmaMatrixOperator_real_symmetric (M : Matrix σ σ ℂ) (hM : M.conjTranspose = M)
    (x y : EuclideanSpace ℂ σ) :
    ⟪x,qmaMatrixOperator M y⟫_ℝ = ⟪qmaMatrixOperator M x,y⟫_ℝ := by
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right (qmaMatrixOperator M) x y
  rw [← qmaMatrixOperator_star,hM] at h
  exact congrArg Complex.re h

theorem qmaMediatorRestriction_apply (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) (s : σ) :
    qmaMediatorRestriction x s = x (s,qmaAncillaVacuum) := by
  change (∑ t, (qmaMediatorVacuumColumn (σ := σ) (κ := κ)).conjTranspose s t*x t) = _
  simp [Matrix.conjTranspose_apply,qmaMediatorVacuumColumn,qmaSliceColumn,
    Fintype.sum_prod_type,Matrix.one_apply,apply_ite]

def qmaPhysicalOperator (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (qmaMatrixOperator (qmaPhysicalMediatorMatrix g C D V)).restrictScalars ℝ

def qmaPerturbationOperator (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (qmaMatrixOperator (qmaMediatorPerturbation C D V)).restrictScalars ℝ

def qmaCouplingOperator (V : κ → Matrix σ σ ℂ) :
    EuclideanSpace ℂ σ →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (qmaMatrixOperator (qmaAncillaColumn V)).restrictScalars ℝ

def qmaComplementOperator (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  qmaMediatorHighProjection.comp ((qmaPerturbationOperator C D V).comp qmaMediatorHighProjection)

theorem qmaPhysicalOperator_low (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (p : EuclideanSpace ℂ σ) :
    qmaPhysicalOperator g C D V (qmaMediatorInclusion p) =
      qmaMediatorInclusion (qmaMatrixOperator C p)+qmaCouplingOperator V p := by
  have hm := qmaPhysicalMediator_vacuum g C D V
  have ho := congrArg (fun M : Matrix (σ × (κ → Fin 2)) σ ℂ => qmaMatrixOperator M p) hm
  simp only [qmaMatrixOperator_mul,qmaMatrixOperator_add,ContinuousLinearMap.comp_apply,
    _root_.add_apply] at ho
  exact ho

theorem qmaPhysicalPenalty_high (g : ℝ) (x : EuclideanSpace ℂ (σ × (κ → Fin 2)))
    (hx : qmaMediatorRestriction x = 0) :
    qmaMatrixOperator (qmaPhysicalPenaltyMatrix g) x = qmaPaddedPenalty g x := by
  have he := qmaAncillaDiagonal_real_operator (σ := σ) (κ := κ)
    (fun a => g*qmaAncillaNumber a)
  have hp := congrArg (fun f : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) => f x) he
  change qmaMatrixOperator (qmaPhysicalPenaltyMatrix g) x = _ at hp
  rw [hp]
  ext p
  by_cases ha : p.2 = qmaAncillaVacuum
  · have hzero := congrArg (fun u : EuclideanSpace ℂ σ => u p.1) hx
    rw [qmaMediatorRestriction_apply] at hzero
    change x (p.1,qmaAncillaVacuum) = 0 at hzero
    have hxp : x p = 0 := by
      change x (p.1,p.2) = 0
      rw [ha]
      exact hzero
    simp [qmaPaddedPenalty,diagonalPenalty_apply,hxp]
  · simp [qmaPaddedPenalty,diagonalPenalty_apply,qmaPaddedWeight,qmaPaddedExcitationNumber,ha]

theorem qmaComplementOperator_form (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) (hx : qmaMediatorRestriction x = 0) :
    ⟪x,qmaComplementOperator C D V x⟫_ℝ = ⟪x,qmaPerturbationOperator C D V x⟫_ℝ := by
  have hQx : qmaMediatorHighProjection x = x := by
    rw [← qmaMediator_highPart]
    simp [Perturbation.orthogonalHighPart,hx]
  have hs := qmaMatrixOperator_real_symmetric
    (qmaMediatorHighMatrix (σ := σ) (κ := κ)) qmaMediatorHigh_star x
    (qmaPerturbationOperator C D V x)
  change ⟪x,qmaMediatorHighProjection (qmaPerturbationOperator C D V
    (qmaMediatorHighProjection x))⟫_ℝ = _
  rw [hQx]
  change ⟪x,qmaMediatorHighProjection (qmaPerturbationOperator C D V x)⟫_ℝ =
    ⟪qmaMediatorHighProjection x,qmaPerturbationOperator C D V x⟫_ℝ at hs
  simpa only [hQx] using hs

theorem qmaPhysicalOperator_high (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) (hx : qmaMediatorRestriction x = 0) :
    ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ =
      Perturbation.penaltyForm (qmaPaddedPenalty g) x+⟪x,qmaComplementOperator C D V x⟫_ℝ := by
  have he : qmaPhysicalOperator g C D V x =
      qmaMatrixOperator (qmaPhysicalPenaltyMatrix g) x+qmaPerturbationOperator C D V x := by
    change qmaMatrixOperator (_+_) x = _
    rw [qmaMatrixOperator_add,_root_.add_apply]
    rfl
  rw [he,qmaPhysicalPenalty_high g x hx,inner_add_right,qmaComplementOperator_form C D V x hx]
  rfl

theorem qmaPhysicalOperator_energy (g : ℝ) (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hC : C.conjTranspose = C) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    ⟪x,qmaPhysicalOperator g C D V x⟫_ℝ =
      Perturbation.lowBlockEnergy ((qmaMatrixOperator C).restrictScalars ℝ) (qmaPaddedPenalty g)
        (qmaComplementOperator C D V) (qmaCouplingOperator V) (qmaMediatorRestriction x)
        (qmaMediatorHighProjection x) := by
  rw [← qmaMediator_highPart]
  apply Perturbation.orthogonalBlock_full_energy
    (qmaMediatorInclusion (σ := σ) (κ := κ)) (qmaMediatorRestriction (σ := σ) (κ := κ))
    (qmaPhysicalOperator g C D V) (qmaPaddedPenalty g) (qmaComplementOperator C D V)
    ((qmaMatrixOperator C).restrictScalars ℝ) (qmaCouplingOperator V)
  · exact qmaMediator_restrict_include
  · exact qmaMediator_inclusion_adjoint
  · exact qmaMatrixOperator_real_symmetric _ (qmaPhysicalMediator_star g C D V hC hD hV)
  · exact qmaPhysicalOperator_low g C D V
  · exact qmaMediatorRestriction_column V
  · exact qmaPhysicalOperator_high g C D V

end ContinuumCoulomb

end

end OAI
