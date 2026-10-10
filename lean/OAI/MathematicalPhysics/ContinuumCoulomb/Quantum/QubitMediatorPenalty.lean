import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorProjection

namespace OAI

/-! An invertible diagonal extension of the physical excitation penalty.
The extension agrees with the physical penalty on the actual complement. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaPaddedExcitationNumber (a : κ → Fin 2) : ℕ :=
  if a = qmaAncillaVacuum then 1 else qmaAncillaNumber a

omit [DecidableEq κ] in
theorem qmaPaddedExcitationNumber_pos (a : κ → Fin 2) : 0 < qmaPaddedExcitationNumber a := by
  unfold qmaPaddedExcitationNumber
  split_ifs with h
  · exact Nat.zero_lt_one
  · exact qmaAncillaNumber_pos a h

theorem qmaPaddedExcitationNumber_single (e : κ) :
    qmaPaddedExcitationNumber (qmaAncillaSingle e) = 1 := by
  simp [qmaPaddedExcitationNumber,qmaAncillaSingle_ne_vacuum]

def qmaPaddedWeight (g : ℝ) (p : σ × (κ → Fin 2)) : ℝ :=
  g*qmaPaddedExcitationNumber p.2

def qmaPaddedPenalty (g : ℝ) : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) := diagonalPenalty (qmaPaddedWeight g)

def qmaPaddedInverse (g : ℝ) : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) := diagonalPenalty (fun p => (qmaPaddedWeight g p)⁻¹)

omit [DecidableEq σ] in
theorem qmaPaddedPenalty_gap {g : ℝ} (hg : 0 < g) (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    g*‖x‖^2 ≤ ⟪x,qmaPaddedPenalty g x⟫_ℝ := by
  apply diagonalPenalty_gap
  intro p
  have hn : (1:ℝ) ≤ qmaPaddedExcitationNumber p.2 := by
    exact_mod_cast qmaPaddedExcitationNumber_pos p.2
  exact (mul_one g).ge.trans (mul_le_mul_of_nonneg_left hn hg.le)

omit [DecidableEq σ] in
theorem qmaPaddedPenalty_inverse {g : ℝ} (hg : 0 < g)
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) : qmaPaddedPenalty g (qmaPaddedInverse g x) = x := by
  apply diagonalPenalty_inverse_right
  intro p
  have hn : (0:ℝ) < qmaPaddedExcitationNumber p.2 := by exact_mod_cast qmaPaddedExcitationNumber_pos p.2
  exact ne_of_gt (mul_pos hg hn)

omit [DecidableEq σ] in
theorem qmaPaddedInverse_norm {g : ℝ} (hg : 0 < g) :
    ‖qmaPaddedInverse (σ := σ) (κ := κ) g‖ ≤ 1/g := by
  apply diagonalPenalty_inverse_norm hg
  intro p
  have hn : (1:ℝ) ≤ qmaPaddedExcitationNumber p.2 := by
    exact_mod_cast qmaPaddedExcitationNumber_pos p.2
  exact (mul_one g).ge.trans (mul_le_mul_of_nonneg_left hn hg.le)

theorem qmaAncillaDiagonal_real_operator (w : (κ → Fin 2) → ℝ) :
    (qmaMatrixOperator (qmaAncillaDiagonal (σ := σ) (fun a => (w a : ℂ)))).restrictScalars ℝ =
      diagonalPenalty (fun p : σ × (κ → Fin 2) => w p.2) := by
  ext x p
  change qmaMatrixOperator (qmaAncillaDiagonal (fun a => (w a : ℂ))) x p = w p.2 • x p
  rw [qmaAncillaDiagonal_eq]
  simp [qmaMatrixOperator_apply,Matrix.diagonal_apply,RCLike.real_smul_eq_coe_mul]

theorem qmaPaddedInverse_column (g : ℝ) (V : κ → Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ) :
    qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) x) =
      g⁻¹ • qmaMatrixOperator (qmaAncillaColumn V) x := by
  have hw (e : κ) : ((g*qmaPaddedExcitationNumber (qmaAncillaSingle e) : ℝ)⁻¹ : ℂ) =
      (g⁻¹ : ℝ) := by rw [qmaPaddedExcitationNumber_single]; simp
  have hm := qmaAncillaDiagonal_column
    (σ := σ) (fun a => ((g*qmaPaddedExcitationNumber a : ℝ)⁻¹ : ℂ)) V (g⁻¹ : ℝ) hw
  have ho := congrArg (fun M : Matrix (σ × (κ → Fin 2)) σ ℂ => qmaMatrixOperator M x) hm
  rw [qmaMatrixOperator_mul,qmaMatrixOperator_smul] at ho
  have he := qmaAncillaDiagonal_real_operator (σ := σ) (κ := κ)
    (fun a => (g*qmaPaddedExcitationNumber a : ℝ)⁻¹)
  have heapp := congrArg (fun f : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) => f (qmaMatrixOperator (qmaAncillaColumn V) x)) he
  change qmaMatrixOperator _ (qmaMatrixOperator (qmaAncillaColumn V) x) =
    qmaPaddedInverse g (qmaMatrixOperator (qmaAncillaColumn V) x) at heapp
  simp only [Complex.ofReal_inv] at heapp
  rw [ContinuousLinearMap.comp_apply,heapp,_root_.smul_apply] at ho
  exact ho

end ContinuumCoulomb

end

end OAI
