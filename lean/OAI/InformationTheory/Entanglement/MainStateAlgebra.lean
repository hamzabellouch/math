import OAI.Analysis.Quantum.PPTSquare.ExplicitMaps
import OAI.Analysis.Quantum.PPTSquare.PairResult
import OAI.InformationTheory.Entanglement.ChoiTransfer
import OAI.InformationTheory.Entanglement.SecretDefinitions

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
lemma sharp_ppt {F : Map n m} (hF : PPT F) : PPT (sharp F) := by
  exact ppt_output_transpose (ppt_input_transpose (ppt_hsAdjoint hF))
omit [Fintype n] [DecidableEq n] in
lemma projector_real_smul (r : ℝ) (v : n → ℂ) :
    projector ((r : ℂ) • v)=((r^2 : ℝ) : ℂ) • projector v := by
  ext i j
  simp only [projector,Matrix.vecMulVec_apply,Pi.smul_apply,Pi.star_apply,smul_eq_mul,
    star_mul,Complex.star_def,Complex.conj_ofReal,Matrix.smul_apply,Complex.ofReal_pow]
  ring
omit [DecidableEq n] in
lemma psd_trace_re_pos {A : Mat n} (hA : A.PosSemidef) (hne : A ≠ 0) :
    0 < (Matrix.trace A).re := by
  have ht := Complex.nonneg_iff.mp hA.trace_nonneg
  apply lt_of_le_of_ne ht.1
  intro h
  apply hne
  apply hA.trace_eq_zero_iff.mp
  apply Complex.ext
  · exact h.symm
  · exact ht.2.symm
omit [DecidableEq n] in
lemma psd_trace_ofReal {A : Mat n} (hA : A.PosSemidef) :
    ((Matrix.trace A).re : ℂ)=Matrix.trace A := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hA.trace_nonneg).2
omit [DecidableEq n] in
lemma normalized_psd {A : Mat n} (hA : A.PosSemidef) :
    ((((Matrix.trace A).re)⁻¹ : ℝ) : ℂ) • A |>.PosSemidef :=
  hA.smul (by exact_mod_cast inv_nonneg.mpr (Complex.nonneg_iff.mp hA.trace_nonneg).1)
omit [DecidableEq n] in
lemma normalized_trace {A : Mat n} (hA : A.PosSemidef) (hne : A ≠ 0) :
    Matrix.trace (((((Matrix.trace A).re)⁻¹ : ℝ) : ℂ) • A)=1 := by
  rw [Matrix.trace_smul,smul_eq_mul,Complex.ofReal_inv,psd_trace_ofReal hA]
  exact inv_mul_cancel₀ (fun h => hne (hA.trace_eq_zero_iff.mp h))
end SecretKey

namespace ExplicitPencil
open ChannelCompletion TensorCriterion SecretKey

def stateTrace : ℝ := (Matrix.trace (Z L)).re

def rho : Mat (Fin 10 × Fin 10) := ((stateTrace⁻¹ : ℝ) : ℂ) • Z L

def stateVector : Fin 10 × Fin 10 → ℂ :=
  (((Real.sqrt stateTrace)⁻¹ : ℝ) : ℂ) • omega
lemma Z_psd : (Z L).PosSemidef := cp_choi (cp_comp main_pair.2.1.1 main_pair.1.1)
lemma stateTrace_pos : 0 < stateTrace := psd_trace_re_pos Z_psd main_pair.2.2.1
lemma rho_psd : rho.PosSemidef := normalized_psd Z_psd
lemma rho_trace : Matrix.trace rho=1 := normalized_trace Z_psd main_pair.2.2.1
lemma rho_ne_zero : rho ≠ 0 := by
  intro h
  have hh := rho_trace
  rw [h,Matrix.trace_zero] at hh
  exact zero_ne_one hh
lemma rho_no_product (u v : Fin 10 → ℂ)
    (h : ∃ w, rho.mulVec w=product u v) : product u v=0 := by
  obtain ⟨w,hw⟩ := h
  apply main_pair.2.2.2.1 u v
  refine ⟨((stateTrace⁻¹ : ℝ) : ℂ) • w, ?_⟩
  rw [Matrix.mulVec_smul]
  simpa only [rho,Matrix.smul_mulVec] using hw
lemma rho_entangled : ¬ Separable rho := by
  intro h
  obtain ⟨u,v,hne,w,hw⟩ := separable_nonzero_product h rho_ne_zero
  exact hne (rho_no_product u v ⟨w,hw⟩)
lemma stateVector_projector : projector stateVector=
    ((stateTrace⁻¹ : ℝ) : ℂ) • projector (omega (n := Fin 10)) := by
  rw [stateVector,projector_real_smul,inv_pow,Real.sq_sqrt stateTrace_pos.le]
lemma rho_identification : rho=tensorMap (sharp (Phi1 L)) (Phi2 L) (projector stateVector) := by
  rw [stateVector_projector,map_smul,← choi_transfer main_pair.1.1]
  rfl
lemma rho_represented : Represented rho := by
  refine ⟨rho_psd,rho_trace,10,10,by norm_num,by norm_num,
    sharp (Phi1 L),Phi2 L,stateVector,(sharp_ppt main_pair.1).1,
    (ppt_input_transpose (sharp_ppt main_pair.1)).1,main_pair.2.1.1,
    (ppt_input_transpose main_pair.2.1).1,rho_identification⟩

theorem main_state_algebra : rho.PosSemidef ∧ Matrix.trace rho=1 ∧
    rho ≠ 0 ∧ (∀ u v : Fin 10 → ℂ,
      (∃ w, rho.mulVec w=product u v) → product u v=0) ∧
    ¬ Separable rho ∧ Represented rho ∧
    rho=tensorMap (sharp (Phi1 L)) (Phi2 L) (projector stateVector) :=
  ⟨rho_psd,rho_trace,rho_ne_zero,rho_no_product,rho_entangled,rho_represented,rho_identification⟩

end ExplicitPencil

end

end OAI
