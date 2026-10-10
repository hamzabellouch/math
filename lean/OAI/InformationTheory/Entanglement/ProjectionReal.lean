import OAI.InformationTheory.Entanglement.ProjectionMain
import OAI.InformationTheory.Entanglement.ChoiTransfer

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace ProjectionCriterion
open ChannelCompletion TensorCriterion SecretKey
namespace Data
variable {Q K D I : Type} [Fintype Q] [Fintype K] [Fintype D] [Fintype I]
  [DecidableEq Q] [DecidableEq K] [DecidableEq D] [DecidableEq I]
variable (d : Data Q K D I)

def RealProjections : Prop := ∀ i a b, (d.P i a b).im=0
omit [DecidableEq K] [DecidableEq I] in
lemma P_transpose (hr : d.RealProjections) (i : I) : (d.P i)ᵀ=d.P i := by
  ext a b
  have he := (d.hermitian i).apply a b
  rw [Complex.ext_iff] at he ⊢
  exact ⟨he.1,by change (d.P i b a).im=(d.P i a b).im; rw [hr i b a,hr i a b]⟩
omit [DecidableEq K] [DecidableEq I] in
lemma H_transpose (hr : d.RealProjections) (i j : I) : (d.H i j)ᵀ=d.H i j := by
  simp only [H,Matrix.transpose_smul,Matrix.transpose_mul,d.P_transpose hr]
  by_cases hc : d.c i j=0
  · simp [hc]
  · rw [d.commute i j hc]
omit [DecidableEq K] in
lemma adjoint_input_transpose (hr : d.RealProjections) :
    (hsAdjoint d.Psi).comp transposeMap=hsAdjoint d.Psi := by
  ext A i j
  change hsAdjoint d.Psi Aᵀ i j=hsAdjoint d.Psi A i j
  simp only [d.adjoint_apply,(d.H_hermitian i j).eq]
  rw [← d.H_transpose hr i j,Matrix.trace_transpose_mul,d.H_transpose hr i j]
omit [DecidableEq K] in
lemma adjoint_trace (A : Mat D) :
    Matrix.trace (hsAdjoint d.Psi A)=(Fintype.card Q : ℂ)*Matrix.trace A := by
  change (∑ i, hsAdjoint d.Psi A i i)=_
  simp_rw [d.adjoint_apply,d.H_self,(d.hermitian _).eq,Matrix.trace_mul_comm (d.P _) A]
  simpa only [one_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    using d.weighted_trace (fun _ => 1) A
omit [DecidableEq K] in
lemma choi_real (hr : d.RealProjections) :
    d.C=tensorMap (hsAdjoint d.Psi) (hsAdjoint d.Psi) (projector (omega (n := D))) := by
  change choi ((hsAdjoint d.Psi).comp d.Psi)=_
  rw [choi_transfer d.Psi_cp]
  have he : sharp d.Psi=hsAdjoint d.Psi := by
    rw [sharp,d.adjoint_input_transpose hr,d.adjoint_output_transpose]
  rw [he]

def localChannel : Map D I := (((Fintype.card Q : ℝ)⁻¹ : ℝ) : ℂ) • hsAdjoint d.Psi
def rho : Mat (I × I) := ((((Fintype.card Q : ℝ)^2*(Fintype.card D : ℝ))⁻¹ : ℝ) : ℂ) • d.C

omit [DecidableEq K] in
lemma localChannel_ppt : PPT d.localChannel := by
  refine ⟨cp_smul d.adjoint_ppt.1 (inv_nonneg.mpr (Nat.cast_nonneg _)),?_⟩
  change CP ((((Fintype.card Q : ℝ)⁻¹ : ℝ) : ℂ) • (transposeMap.comp (hsAdjoint d.Psi)))
  exact cp_smul d.adjoint_ppt.2 (inv_nonneg.mpr (Nat.cast_nonneg _))
omit [DecidableEq K] in
lemma localChannel_tp [Nonempty Q] : TracePreserving d.localChannel := by
  intro A
  change Matrix.trace ((((Fintype.card Q : ℝ)⁻¹ : ℝ) : ℂ) • hsAdjoint d.Psi A)=_
  rw [Matrix.trace_smul,d.adjoint_trace,smul_eq_mul]
  have hq : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  push_cast
  field_simp

omit [DecidableEq K] in
lemma rho_psd : d.rho.PosSemidef :=
  (cp_choi (cp_comp d.adjoint_ppt.1 d.Psi_cp)).smul (by
    change (0 : ℂ) ≤ (((Fintype.card Q : ℝ)^2*(Fintype.card D : ℝ))⁻¹ : ℝ)
    have hn : 0 ≤ ((Fintype.card Q : ℝ)^2*(Fintype.card D : ℝ))⁻¹ := by positivity
    exact_mod_cast hn)
omit [DecidableEq K] in
lemma rho_trace [Nonempty Q] [Nonempty D] : Matrix.trace d.rho=1 := by
  rw [rho,Matrix.trace_smul,d.C_trace,smul_eq_mul]
  have hq : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hd : (Fintype.card D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  push_cast
  field_simp

omit [Fintype I] [DecidableEq I] in
lemma separable_scaling {Z : Mat (I × I)} (hZ : Separable Z) {a : ℝ} (ha : 0 ≤ a) :
    Separable ((a : ℂ) • Z) := by
  obtain ⟨r,A,B,hA,hB,rfl⟩ := hZ
  refine ⟨r,fun i => (a : ℂ) • A i,B,fun i => (hA i).smul (by exact_mod_cast ha),hB,?_⟩
  simp only [Finset.smul_sum,Matrix.smul_kronecker]
lemma rho_nonseparable [Nonempty Q] [Nonempty K] [Nonempty D] : ¬ Separable d.rho := by
  intro h
  have hq : (Fintype.card Q : ℝ)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hd : (Fintype.card D : ℝ)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hz := separable_scaling h (mul_nonneg (sq_nonneg (Fintype.card Q : ℝ)) (Nat.cast_nonneg (Fintype.card D)))
  have he : ((((Fintype.card Q : ℝ)^2*(Fintype.card D : ℝ)) : ℝ) : ℂ) • d.rho=d.C := by
    rw [rho,smul_smul,← Complex.ofReal_mul,mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero _ hq) hd)]
    simp
  rw [he] at hz
  exact d.C_nonseparable hz
end Data
end ProjectionCriterion

end

end OAI
