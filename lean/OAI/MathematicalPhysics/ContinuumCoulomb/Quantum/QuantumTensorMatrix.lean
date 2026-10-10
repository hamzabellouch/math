import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourDoubleGap

namespace OAI

/-! Finite tensor matrices used to place the proved four-spin code at every site. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical ComplexOrder
variable {Q σ τ υ : Type*} [Fintype Q] [DecidableEq Q] [Fintype σ] [Fintype τ] [Fintype υ]

def qmaTensorMatrix (A : Q → Matrix σ τ ℂ) : Matrix (Q → σ) (Q → τ) ℂ :=
  fun s t => ∏ i, A i (s i) (t i)

omit [Fintype σ] [Fintype υ] in
theorem qmaTensorMatrix_mul (A : Q → Matrix σ τ ℂ) (B : Q → Matrix τ υ ℂ) :
    qmaTensorMatrix A*qmaTensorMatrix B = qmaTensorMatrix (fun i => A i*B i) := by
  ext s t
  change (∑ r : Q → τ, (∏ i, A i (s i) (r i))*(∏ i, B i (r i) (t i))) = _
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => A i (s i) a*B i a (t i))).symm

omit [Fintype σ] [Fintype τ] [DecidableEq Q] in
theorem qmaTensorMatrix_star (A : Q → Matrix σ τ ℂ) :
    (qmaTensorMatrix A).conjTranspose = qmaTensorMatrix (fun i => (A i).conjTranspose) := by
  ext s t
  simp [qmaTensorMatrix,Matrix.conjTranspose_apply]

variable [DecidableEq σ]

omit [Fintype σ] [DecidableEq Q] in
theorem qmaTensorMatrix_one : qmaTensorMatrix (fun _ : Q => (1 : Matrix σ σ ℂ)) = 1 := by
  ext s t
  simp only [qmaTensorMatrix,Matrix.one_apply]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [Fintype τ] [DecidableEq σ] in
theorem qmaTensorMatrix_gram [DecidableEq τ] (A : Q → Matrix σ τ ℂ)
    (hA : ∀ i, (A i).conjTranspose*A i = 1) :
    (qmaTensorMatrix A).conjTranspose*qmaTensorMatrix A = 1 := by
  rw [qmaTensorMatrix_star,qmaTensorMatrix_mul]
  simpa only [hA] using (qmaTensorMatrix_one (Q := Q) (σ := τ))

omit [DecidableEq σ] in
theorem qmaTensorMatrix_projector (P : Q → Matrix σ σ ℂ)
    (hP : ∀ i, (P i).conjTranspose = P i) (hPP : ∀ i, P i*P i = P i) :
    (qmaTensorMatrix P).conjTranspose*qmaTensorMatrix P = qmaTensorMatrix P := by
  rw [qmaTensorMatrix_star,qmaTensorMatrix_mul]
  simp only [hP,hPP]

omit [DecidableEq σ] in
theorem qmaTensorMatrix_projector_posSemidef (P : Q → Matrix σ σ ℂ)
    (hP : ∀ i, (P i).conjTranspose = P i) (hPP : ∀ i, P i*P i = P i) :
    (qmaTensorMatrix P).PosSemidef := by
  rw [← qmaTensorMatrix_projector P hP hPP]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem qmaTensorMatrix_complement_posSemidef (P : Q → Matrix σ σ ℂ)
    (hP : ∀ i, (P i).conjTranspose = P i) (hPP : ∀ i, P i*P i = P i) :
    (1-qmaTensorMatrix P).PosSemidef := by
  have hstar : (qmaTensorMatrix P).conjTranspose = qmaTensorMatrix P := by
    rw [qmaTensorMatrix_star]
    simp only [hP]
  have hs : qmaTensorMatrix P*qmaTensorMatrix P = qmaTensorMatrix P := by
    simpa only [hstar] using qmaTensorMatrix_projector P hP hPP
  have he : (1-qmaTensorMatrix P).conjTranspose*(1-qmaTensorMatrix P) = 1-qmaTensorMatrix P := by
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hstar]
    noncomm_ring [hs]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def qmaSiteMatrix (i : Q) (A : Matrix σ σ ℂ) : Matrix (Q → σ) (Q → σ) ℂ :=
  qmaTensorMatrix (fun j => if j = i then A else 1)

theorem qmaSiteMatrix_mul (i : Q) (A B : Matrix σ σ ℂ) :
    qmaSiteMatrix i A*qmaSiteMatrix i B = qmaSiteMatrix i (A*B) := by
  rw [qmaSiteMatrix,qmaSiteMatrix,qmaTensorMatrix_mul]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

omit [Fintype σ] in
theorem qmaSiteMatrix_one (i : Q) : qmaSiteMatrix i (1 : Matrix σ σ ℂ) = 1 := by
  simp only [qmaSiteMatrix,ite_self,qmaTensorMatrix_one]

omit [Fintype σ] in
theorem qmaSiteMatrix_star (i : Q) (A : Matrix σ σ ℂ) :
    (qmaSiteMatrix i A).conjTranspose = qmaSiteMatrix i A.conjTranspose := by
  rw [qmaSiteMatrix,qmaTensorMatrix_star]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

omit [Fintype σ] in
theorem qmaSiteMatrix_apply (i : Q) (A : Matrix σ σ ℂ) (s t : Q → σ) :
    qmaSiteMatrix i A s t = A (s i) (t i)*
      ∏ j ∈ Finset.univ.erase i, if s j = t j then (1:ℂ) else 0 := by
  unfold qmaSiteMatrix qmaTensorMatrix
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [(Finset.mem_erase.mp hj).1,Matrix.one_apply]

omit [Fintype σ] in
theorem qmaSiteMatrix_add (i : Q) (A B : Matrix σ σ ℂ) :
    qmaSiteMatrix i (A+B) = qmaSiteMatrix i A+qmaSiteMatrix i B := by
  ext s t
  simp only [qmaSiteMatrix_apply,Matrix.add_apply,add_mul]

omit [Fintype σ] in
theorem qmaSiteMatrix_smul (i : Q) (c : ℂ) (A : Matrix σ σ ℂ) :
    qmaSiteMatrix i (c • A) = c • qmaSiteMatrix i A := by
  ext s t
  simp only [qmaSiteMatrix_apply,Matrix.smul_apply,smul_eq_mul,mul_assoc]

end ContinuumCoulomb

end

end OAI
