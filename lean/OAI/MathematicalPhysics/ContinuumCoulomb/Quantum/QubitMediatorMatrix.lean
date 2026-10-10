import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAncillaCompression

namespace OAI

/-! The literal parallel mediator Hamiltonian and its exact first three
vacuum-compressed terms. Single flips have zero third-order compression. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaMediatorFlips (V : κ → Matrix σ σ ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ∑ e, V e ⊗ₖ qmaBitFlipMatrix e

def qmaMediatorOccupations (D : κ → Matrix σ σ ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  ∑ e, D e ⊗ₖ qmaAncillaOccupation e

def qmaMediatorPerturbation (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  C ⊗ₖ 1 + qmaMediatorOccupations D + qmaMediatorFlips V

theorem qmaMediatorFlips_vacuum (V : κ → Matrix σ σ ℂ) :
    qmaMediatorFlips V*qmaSliceColumn (qmaAncillaVacuum (κ := κ)) 1 = qmaAncillaColumn V := by
  unfold qmaMediatorFlips qmaAncillaColumn
  rw [Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ext s t
  rcases s with ⟨s,a⟩
  rw [qmaSliceColumn_kronecker_apply,qmaBitFlipMatrix_vacuum_right,Matrix.mul_one]
  simp only [qmaSliceColumn,ite_mul,one_mul,zero_mul]

theorem qmaMediatorOccupations_vacuum (D : κ → Matrix σ σ ℂ) :
    qmaMediatorOccupations D*qmaSliceColumn (qmaAncillaVacuum (κ := κ)) (1 : Matrix σ σ ℂ) = 0 := by
  unfold qmaMediatorOccupations
  rw [Matrix.sum_mul]
  apply Finset.sum_eq_zero
  intro e _
  ext s t
  rcases s with ⟨s,a⟩
  rw [qmaSliceColumn_kronecker_apply,qmaAncillaOccupation_vacuum_right,zero_mul]
  rfl

omit [DecidableEq σ] in
theorem qmaAncillaColumn_identity (V W : κ → Matrix σ σ ℂ) (C : Matrix σ σ ℂ) :
    (qmaAncillaColumn V).conjTranspose*(C ⊗ₖ 1)*qmaAncillaColumn W =
      ∑ e, (V e).conjTranspose*C*W e := by
  rw [qmaAncillaColumn_sandwich]
  simp only [Matrix.one_apply,qmaAncillaSingle_injective.eq_iff,ite_smul,one_smul,zero_smul]
  simp

omit [DecidableEq σ] in
theorem qmaMediatorPerturbation_compression (C : Matrix σ σ ℂ)
    (D V W Z : κ → Matrix σ σ ℂ) :
    (qmaAncillaColumn W).conjTranspose*qmaMediatorPerturbation C D V*qmaAncillaColumn Z =
      (∑ e, (W e).conjTranspose*C*Z e)+(∑ e, (W e).conjTranspose*D e*Z e) := by
  unfold qmaMediatorPerturbation qmaMediatorOccupations qmaMediatorFlips
  rw [Matrix.mul_add,Matrix.mul_add,Matrix.add_mul,Matrix.add_mul,qmaAncillaColumn_identity,
    Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_sum,Matrix.sum_mul]
  simp only [qmaAncillaColumn_occupation,qmaAncillaColumn_flip,Finset.sum_const_zero,add_zero]

def qmaAncillaDiagonal (w : (κ → Fin 2) → ℂ) :
    Matrix (σ × (κ → Fin 2)) (σ × (κ → Fin 2)) ℂ :=
  1 ⊗ₖ Matrix.diagonal w

theorem qmaAncillaDiagonal_slice (w : (κ → Fin 2) → ℂ) (a : κ → Fin 2)
    (A : Matrix σ σ ℂ) :
    qmaAncillaDiagonal w*qmaSliceColumn a A = w a • qmaSliceColumn a A := by
  ext s t
  rcases s with ⟨s,b⟩
  rw [qmaAncillaDiagonal,qmaSliceColumn_kronecker_apply,Matrix.one_mul]
  by_cases h : b = a
  · subst b
    simp [qmaSliceColumn]
  · simp [qmaSliceColumn,h]

theorem qmaAncillaDiagonal_column (w : (κ → Fin 2) → ℂ) (V : κ → Matrix σ σ ℂ)
    (c : ℂ) (hw : ∀ e, w (qmaAncillaSingle e) = c) :
    qmaAncillaDiagonal w*qmaAncillaColumn V = c • qmaAncillaColumn V := by
  unfold qmaAncillaColumn
  rw [Matrix.mul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [qmaAncillaDiagonal_slice,hw]

def qmaAncillaInverseWeight (g : ℂ) (a : κ → Fin 2) : ℂ :=
  if a = qmaAncillaVacuum then 0 else (g*(qmaAncillaNumber a : ℂ))⁻¹

theorem qmaAncillaInverseWeight_single (g : ℂ) (e : κ) :
    qmaAncillaInverseWeight g (qmaAncillaSingle e) = g⁻¹ := by
  simp [qmaAncillaInverseWeight,qmaAncillaSingle_ne_vacuum]

theorem qmaAncillaInverse_column (g : ℂ) (V : κ → Matrix σ σ ℂ) :
    qmaAncillaDiagonal (qmaAncillaInverseWeight g)*qmaAncillaColumn V =
      g⁻¹ • qmaAncillaColumn V :=
  qmaAncillaDiagonal_column _ _ _ (qmaAncillaInverseWeight_single g)

end ContinuumCoulomb

end

end OAI
