import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEntryParity
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionLocalFamily

namespace OAI

/-! The selected phases make every subdivision output term a real matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ τ κ ι α : Type*}

theorem QMAEntryParity.sum {β : Type*} [Fintype β] {p : Bool} (M : β → Matrix σ σ ℂ)
    (hM : ∀ b, QMAEntryParity p (M b)) : QMAEntryParity p (∑ b, M b) := by
  cases p <;> simp only [QMAEntryParity,Bool.false_eq_true,ite_false,ite_true] at *
  · intro s t
    simp only [Matrix.sum_apply]
    change Complex.imAddGroupHom (∑ b, M b s t) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun b _ => hM b s t)
  · intro s t
    simp only [Matrix.sum_apply]
    change Complex.reAddGroupHom (∑ b, M b s t) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun b _ => hM b s t)

theorem qmaIdentity_real [DecidableEq σ] : QMAEntryParity false (1 : Matrix σ σ ℂ) := by
  intro s t
  simp only [Matrix.one_apply]
  split_ifs <;> norm_num

theorem QMAEntryParity.kronecker {M : Matrix σ σ ℂ} {N : Matrix τ τ ℂ}
    (hM : QMAEntryParity false M) (hN : QMAEntryParity false N) :
    QMAEntryParity false (M ⊗ₖ N) := by
  rintro ⟨s,a⟩ ⟨t,b⟩
  simp only [Matrix.kronecker_apply,Complex.mul_im,hM s t,hN a b,mul_zero,zero_mul,add_zero]

theorem QMAEntryParity.submatrix {p : Bool} {M : Matrix σ σ ℂ}
    (hM : QMAEntryParity p M) (f : τ → σ) : QMAEntryParity p (M.submatrix f f) := by
  cases p <;> exact fun s t => hM (f s) (f t)

variable [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem qmaOccupation_real (e : κ) : QMAEntryParity false (qmaAncillaOccupation e) := by
  intro a b
  simp only [qmaAncillaOccupation,Matrix.diagonal_apply]
  split_ifs <;> norm_num

variable [Fintype ι] [DecidableEq ι] [Fintype α]

omit [Fintype ι] [DecidableEq ι] in
theorem qmaJoinMatrix_real {M : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    {N : Matrix (κ → Fin 2) (κ → Fin 2) ℂ}
    (hM : QMAEntryParity false M) (hN : QMAEntryParity false N) :
    QMAEntryParity false (qmaJoinMatrix M N) :=
  (hM.kronecker hN).submatrix _

omit [Fintype ι] [DecidableEq ι] in
theorem qmaPolarizedJoin_real (M : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (m : κ → Bool) (e : κ) (hM : QMAEntryParity (m e) M) :
    QMAEntryParity false (qmaJoinMatrix M (qmaPolarizedFlip m e)) := by
  exact (show QMAEntryParity false (M ⊗ₖ qmaPolarizedFlip m e) from
    qmaPolarizedTensor_real m e M hM).submatrix _

omit [Fintype α] [DecidableEq ι] in
theorem qmaSubdivisionLocalPiece_real (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool)
    (hA : QMAEntryParity (m e) A) (hB : QMAEntryParity (m e) B) (k : Fin 4) :
    QMAEntryParity false (qmaSubdivisionLocalPiece A B e R j m k) := by
  fin_cases k
  · exact (qmaJoinMatrix_real qmaIdentity_real (qmaOccupation_real e)).real_smul (R^2)
  · exact qmaIdentity_real.real_smul (1+(j/2)^2)
  · exact (qmaPolarizedJoin_real A m e hA).real_smul R
  · exact (qmaPolarizedJoin_real B m e hB).real_smul (-R*j/2)

omit [Fintype α] [DecidableEq ι] in
theorem qmaSubdivisionLocalFamily_real (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool)
    (hF : ∀ a, QMAEntryParity false (F a))
    (hA : ∀ e, QMAEntryParity (m e) (A e)) (hB : ∀ e, QMAEntryParity (m e) (B e))
    (a : α ⊕ (κ × Fin 4)) :
    QMAEntryParity false (qmaSubdivisionLocalFamily F A B R J m a) := by
  cases a with
  | inl a => exact qmaJoinMatrix_real (hF a) qmaIdentity_real
  | inr p => exact qmaSubdivisionLocalPiece_real _ _ _ _ _ _ (hA p.1) (hB p.1) p.2

omit [DecidableEq ι] in
theorem qmaSubdivisionOnQubits_real (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool)
    (hF : ∀ a, QMAEntryParity false (F a))
    (hA : ∀ e, QMAEntryParity (m e) (A e)) (hB : ∀ e, QMAEntryParity (m e) (B e)) :
    QMAEntryParity false (qmaSubdivisionOnQubits (∑ a, F a) A B R J m) := by
  rw [← qmaSubdivisionLocalFamily_sum]
  exact QMAEntryParity.sum _ (qmaSubdivisionLocalFamily_real F A B R J m hF hA hB)

end ContinuumCoulomb

end

end OAI
