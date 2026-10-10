import OAI.InformationTheory.Entanglement.ProjectionReal

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace ProjectionCriterion
open ChannelCompletion TensorCriterion SecretKey

lemma projector_real_smul {n : Type} (r : ℝ) (v : n → ℂ) :
    projector ((r : ℂ) • v)=((r^2 : ℝ) : ℂ) • projector v := by
  ext i j
  simp only [projector,Matrix.vecMulVec_apply,Pi.smul_apply,Pi.star_apply,smul_eq_mul,
    star_mul,Complex.star_def,Complex.conj_ofReal,Matrix.smul_apply,Complex.ofReal_pow]
  ring

def Phi (D : ℕ) : Fin D × Fin D → ℂ := (((Real.sqrt (D : ℝ))⁻¹ : ℝ) : ℂ) • omega
lemma Phi_projector (D : ℕ) : projector (Phi D)=(((D : ℝ)⁻¹ : ℝ) : ℂ) • projector (omega (n := Fin D)) := by
  rw [Phi,projector_real_smul,inv_pow,Real.sq_sqrt (Nat.cast_nonneg D)]

namespace Data
variable {Q K I : Type} [Fintype Q] [Fintype K] [Fintype I]
  [DecidableEq Q] [DecidableEq K] [DecidableEq I]
  [Nonempty Q] [Nonempty K] {D : ℕ} [NeZero D]
variable (d : Data Q K (Fin D) I)
omit [DecidableEq K] [Nonempty Q] [Nonempty K] [NeZero D] in
lemma localChannel_input_transpose (hr : d.RealProjections) :
    d.localChannel.comp transposeMap=d.localChannel := by
  unfold localChannel
  rw [LinearMap.smul_comp,d.adjoint_input_transpose hr]

omit [DecidableEq K] [Nonempty Q] [Nonempty K] [NeZero D] in
lemma rho_identification (hr : d.RealProjections) :
    d.rho=tensorMap d.localChannel d.localChannel (projector (Phi D)) := by
  rw [Phi_projector,localChannel,tensorMap_smul]
  simp only [LinearMap.smul_apply,map_smul,smul_smul]
  rw [← d.choi_real hr]
  unfold rho
  congr 1
  simp only [Fintype.card_fin,Complex.ofReal_inv,Complex.ofReal_natCast,
    Complex.ofReal_mul,mul_inv,pow_two,mul_assoc]
  ring

omit [DecidableEq K] [Nonempty K] in
lemma rho_represented (hr : d.RealProjections) : Represented d.rho := by
  refine ⟨d.rho_psd,d.rho_trace,D,D,Nat.pos_of_ne_zero (NeZero.ne D),
    Nat.pos_of_ne_zero (NeZero.ne D),d.localChannel,d.localChannel,Phi D,
    d.localChannel_ppt.1,?_,d.localChannel_ppt.1,?_,d.rho_identification hr⟩
  all_goals rw [d.localChannel_input_transpose hr]; exact d.localChannel_ppt.1
end Data

theorem real_channel {Q K I : Type} [Fintype Q] [Fintype K] [Fintype I]
    [DecidableEq Q] [DecidableEq K] [DecidableEq I] [Nonempty Q] [Nonempty K]
    {D : ℕ} [NeZero D] (d : Data Q K (Fin D) I) (hr : d.RealProjections) :
    (hsAdjoint d.Psi).comp transposeMap=hsAdjoint d.Psi ∧
    transposeMap.comp (hsAdjoint d.Psi)=hsAdjoint d.Psi ∧
    (∀ A, Matrix.trace (hsAdjoint d.Psi A)=(Fintype.card Q : ℂ)*Matrix.trace A) ∧
    PPT d.localChannel ∧ TracePreserving d.localChannel ∧
    d.rho=tensorMap d.localChannel d.localChannel (projector (Phi D)) ∧
    Represented d.rho ∧ ¬ Separable d.rho := by
  exact ⟨d.adjoint_input_transpose hr,d.adjoint_output_transpose,d.adjoint_trace,
    d.localChannel_ppt,d.localChannel_tp,d.rho_identification hr,d.rho_represented hr,
    d.rho_nonseparable⟩

end ProjectionCriterion

end

end OAI
