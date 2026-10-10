import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorEffective

namespace OAI

/-! Exact effective Hamiltonian of a family of distinct logical edges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {σ τ κ : Type*} [Fintype σ] [Fintype τ] [Fintype κ] [DecidableEq κ]

omit [Fintype τ] [DecidableEq κ] in
theorem qmaOrthogonalColumns_sum_gram (W : κ → Matrix σ τ ℂ)
    (hW : ∀ e f, e ≠ f → (W e).conjTranspose*W f = 0) :
    (∑ e, W e).conjTranspose*(∑ e, W e) = ∑ e, (W e).conjTranspose*W e := by
  simp only [Matrix.conjTranspose_sum,Matrix.sum_mul,Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_eq_single e
  · intro f _ hfe
    exact hW f e hfe
  · intro he
    exact (he (Finset.mem_univ e)).elim

variable {n : ℕ}

theorem qmaFourTensorCoupling_distinct (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ({i,j} : Finset (Fin n)) ≠ {k,l}) (a b c d : Fin 2) (t u : ℝ) :
    (qmaFourTensorCoupling i j a b t*qmaFourTensorEncoding n).conjTranspose*
      (qmaFourTensorCoupling k l c d u*qmaFourTensorEncoding n) = 0 := by
  simp only [qmaFourTensorCoupling,Matrix.smul_mul,Matrix.conjTranspose_smul,
    Matrix.mul_smul,qmaFourTensorWeighted_distinct i j k l hij hkl hne,smul_zero]

def qmaFourTensorFamilyCoupling (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ e, qmaFourTensorCoupling (left e) (right e) (a e) (b e) (t e)

def qmaFourTensorFamilyCounterterm (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ e, qmaFourTensorCounterterm (left e) (right e) (a e) (b e) (t e)

omit [DecidableEq κ] in
theorem qmaFourTensorFamily_effective (left right : κ → Fin n) (a b : κ → Fin 2) (t : κ → ℝ)
    (hneq : ∀ e, left e ≠ right e)
    (hdist : ∀ e f, e ≠ f → ({left e,right e} : Finset (Fin n)) ≠ {left f,right f}) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorFamilyCounterterm left right a b t*
        qmaFourTensorEncoding n +
      (-1/8:ℂ) • ((qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n).conjTranspose*
        (qmaFourTensorFamilyCoupling left right a b t*qmaFourTensorEncoding n)) =
      (∑ e, (t e:ℂ) • qmaPairMatrix (left e) (right e) (qmaFourAxis (a e)) (qmaFourAxis (b e)))+
      ((∑ e, qmaFourEnergyOffset (a e) (b e) (t e):ℝ):ℂ) •
        (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
  have hW (e f : κ) (hef : e ≠ f) :
      (qmaFourTensorCoupling (left e) (right e) (a e) (b e) (t e)*qmaFourTensorEncoding n).conjTranspose*
        (qmaFourTensorCoupling (left f) (right f) (a f) (b f) (t f)*qmaFourTensorEncoding n) = 0 :=
    qmaFourTensorCoupling_distinct _ _ _ _ (hneq e) (hneq f) (hdist e f hef) _ _ _ _ _ _
  simp only [qmaFourTensorFamilyCoupling,Matrix.sum_mul]
  rw [qmaOrthogonalColumns_sum_gram _ hW]
  simp only [qmaFourTensorFamilyCounterterm,Matrix.mul_sum,Matrix.sum_mul,Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  have he (e : κ) := qmaFourTensorCounterterm_effective (left e) (right e) (hneq e) (a e) (b e) (t e)
  simp only [qmaFourTensorEffective] at he
  simp only [he,Finset.sum_add_distrib,← Finset.sum_smul,Complex.ofReal_sum]

end ContinuumCoulomb

end

end OAI
