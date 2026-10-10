import OAI.InformationTheory.Entanglement.TensorTools

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace ProjectionCriterion
open ChannelCompletion TensorCriterion
variable {Q K D I : Type} [Fintype Q] [Fintype K] [Fintype D] [Fintype I]
  [DecidableEq Q] [DecidableEq D] [DecidableEq I]

def correlation (u : Q → K → ℝ) (q r : Q) : ℝ := ∑ a, u q a * u r a

structure Data (Q K D I : Type) [Fintype Q] [Fintype K] [Fintype D] [Fintype I]
    [DecidableEq Q] [DecidableEq D] where
  question : I → Q
  u : Q → K → ℝ
  unit : ∀ q, ∑ a, u q a * u q a = 1
  P : I → Mat D
  hermitian : ∀ i, (P i).IsHermitian
  idempotent : ∀ i, P i * P i = P i
  orthogonal : ∀ i j, question i = question j → i ≠ j → P i * P j = 0
  complete : ∀ q, ∑ i with question i = q, P i = 1
  commute : ∀ i j, correlation u (question i) (question j) ≠ 0 → P i * P j = P j * P i
  κ : ℝ
  gap : κ < (Fintype.card Q : ℝ) / Fintype.card K
  clique : ∀ J : Finset I,
    (∀ i ∈ J, ∀ j ∈ J, i ≠ j → 0 < (Matrix.trace (P i * P j)).re) →
    (J.card : ℝ) ≤ κ

namespace Data
variable (d : Data Q K D I)
def c (i j : I) : ℝ := correlation d.u (d.question i) (d.question j)
def H (i j : I) : Mat D := (d.c i j : ℂ) • (d.P i * d.P j)
def Psi : Map I D where
  toFun X := ∑ i, ∑ j, X i j • d.H i j
  map_add' X Y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a X := by simp [smul_smul,Finset.smul_sum]
def C : Mat (I × I) := choi ((hsAdjoint d.Psi).comp d.Psi)
def B : Mat I := fun i j => d.C (i,i) (j,j)

omit [DecidableEq I] in
lemma c_symm (i j : I) : d.c i j = d.c j i := by
  simp only [c,correlation,mul_comm]
omit [DecidableEq I] in
lemma c_self (i : I) : d.c i i = 1 := d.unit (d.question i)
omit [DecidableEq I] in
lemma P_psd (i : I) : (d.P i).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (d.P i)
  simpa only [(d.hermitian i).eq,d.idempotent] using h
omit [DecidableEq I] in
lemma H_self (i : I) : d.H i i = d.P i := by simp [H,d.c_self,d.idempotent]
omit [DecidableEq I] in
lemma H_symm (i j : I) : d.H i j = d.H j i := by
  by_cases h : d.c i j = 0
  · simp [H,h,← d.c_symm i j]
  · rw [H,H,← d.c_symm i j,d.commute i j h]
omit [DecidableEq I] in
lemma H_adjoint (i j : I) : (d.H i j)ᴴ = d.H j i := by
  simp only [H,Matrix.conjTranspose_smul,Matrix.conjTranspose_mul,
    (d.hermitian i).eq,(d.hermitian j).eq,Complex.star_def,Complex.conj_ofReal,d.c_symm i j]
omit [DecidableEq I] in
lemma H_hermitian (i j : I) : (d.H i j).IsHermitian := by
  rw [Matrix.IsHermitian,d.H_adjoint,d.H_symm]
lemma Psi_single (i j : I) : d.Psi (Matrix.single i j 1) = d.H i j := by
  simp [Psi,Matrix.single_apply,ite_and,ite_smul]
lemma choi_Psi : choi d.Psi = fun a b => d.H a.1 b.1 a.2 b.2 := by
  ext ⟨i,a⟩ ⟨j,b⟩
  exact congrArg (fun X : Mat D => X a b) (d.Psi_single i j)

def gramFactor : Matrix (K × D) (I × D) ℂ :=
  fun a b => (d.u (d.question b.1) a.1 : ℂ) * d.P b.1 a.2 b.2
lemma choi_gram : choi d.Psi = d.gramFactorᴴ * d.gramFactor := by
  rw [d.choi_Psi]
  ext ⟨i,a⟩ ⟨j,b⟩
  change (d.c i j : ℂ) * (∑ e, d.P i a e * d.P j e b) = _
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,gramFactor,star_mul,
    Complex.star_def,Complex.conj_ofReal,Fintype.sum_prod_type]
  have hp (e : D) : star (d.P i e a) = d.P i a e := (d.hermitian i).apply a e
  simp only [← Complex.star_def,hp]
  rw [c,correlation,Complex.ofReal_sum]
  simp only [Complex.ofReal_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro e _
  ring
lemma Psi_cp : CP d.Psi := by
  apply cp_of_choi
  rw [d.choi_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _
omit [DecidableEq I] in
lemma Psi_input_transpose : d.Psi.comp transposeMap = d.Psi := by
  ext X a b
  change (∑ i, ∑ j, X j i • d.H i j) a b = (∑ i, ∑ j, X i j • d.H i j) a b
  rw [Finset.sum_comm]
  simp only [Matrix.sum_apply,Matrix.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [d.H_symm]
lemma Psi_ppt : PPT d.Psi := by
  refine ⟨d.Psi_cp,?_⟩
  have h := cp_simultaneous_transpose d.Psi_cp
  rwa [d.Psi_input_transpose] at h
lemma adjoint_ppt : PPT (hsAdjoint d.Psi) := ppt_hsAdjoint d.Psi_ppt
lemma adjoint_output_transpose : transposeMap.comp (hsAdjoint d.Psi) = hsAdjoint d.Psi := by
  rw [← hsAdjoint_input_transpose,d.Psi_input_transpose]

end Data
end ProjectionCriterion

end

end OAI
