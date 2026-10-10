import OAI.Probability.InvariantIsing.Cavity.CavityBaseSpecialHaar

namespace OAI

/-! Independent rotations inside the base spectral groups preserve the
base interaction and rotate its selected frames. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityGroupRotation {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (U : (a : Fin m) → Orthogonal (k a)) : Orthogonal N := by
  let D := Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))
  refine ⟨D.submatrix e.symm e.symm, (Matrix.mem_orthogonalGroup_iff' _ ℝ).mpr ?_⟩
  change D.transpose.submatrix e.symm e.symm * D.submatrix e.symm e.symm = 1
  rw [Matrix.submatrix_mul_equiv]
  have hD : D.transpose * D = 1 := by
    simp only [D, Matrix.blockDiagonal'_transpose]
    rw [← Matrix.blockDiagonal'_mul]
    have hU : (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ).transpose *
      (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ)) = fun a => (1 : Matrix (Fin (k a)) (Fin (k a)) ℝ) :=
      funext (fun a => (Matrix.mem_orthogonalGroup_iff' (Fin (k a)) ℝ).mp (U a).property)
    rw [hU]
    exact Matrix.blockDiagonal'_one
  rw [hD, Matrix.submatrix_one_equiv]

lemma cavityBlockRotation_conjugate {m : ℕ} (k : Fin m → ℕ)
    (U : (a : Fin m) → Orthogonal (k a)) (lam : Fin m → ℝ) :
    Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ)) *
      Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) *
      (Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))).transpose =
      Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) := by
  rw [← Matrix.blockDiagonal'_diagonal (fun a (_ : Fin (k a)) => lam a),
    Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1
  funext a
  have hU := (Matrix.mem_orthogonalGroup_iff (Fin (k a)) ℝ).mp (U a).property
  have hD : Matrix.diagonal (fun _ : Fin (k a) => lam a) =
      lam a • (1 : Matrix (Fin (k a)) (Fin (k a)) ℝ) := by
    calc
      _ = Matrix.diagonal (lam a • (fun _ : Fin (k a) => (1 : ℝ))) := by
        congr 1
        funext i
        simp
      _ = _ := by rw [Matrix.diagonal_smul, Matrix.diagonal_one]
  rw [hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hU]

lemma cavityGroupRotation_conjugate {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (U : (a : Fin m) → Orthogonal (k a)) (lam : Fin m → ℝ) :
    cavityConjugate (cavityGroupRotation k e U)
      (Matrix.diagonal (fun j => lam (e.symm j).1)) =
      Matrix.diagonal (fun j => lam (e.symm j).1) := by
  have hL : Matrix.diagonal (fun j => lam (e.symm j).1) =
      (Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1)).submatrix
        e.symm e.symm := by
    simpa only [Function.comp_def] using
      (Matrix.submatrix_diagonal_equiv
        (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1) e.symm).symm
  rw [hL]
  change (Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))).submatrix e.symm e.symm *
    (Matrix.diagonal (fun j : Sigma (fun a : Fin m => Fin (k a)) => lam j.1)).submatrix e.symm e.symm *
    (Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))).transpose.submatrix e.symm e.symm = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, cavityBlockRotation_conjugate]

lemma continuous_cavityGroupRotation {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) : Continuous (cavityGroupRotation k e) := by
  have h : Continuous (fun U : (a : Fin m) → Orthogonal (k a) =>
      Matrix.blockDiagonal' (fun a => (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ))) := by
    apply Continuous.matrix_blockDiagonal'
    exact continuous_pi (fun a => continuous_subtype_val.comp (continuous_apply a))
  exact (h.matrix_submatrix e.symm e.symm).subtype_mk _

def cavityGroupFrame {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) : Matrix (Fin N) (Fin (k a)) ℝ :=
  fun i j => if i = e ⟨a, j⟩ then 1 else 0

lemma cavityGroupFrame_mul {N m q : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m)
    (A : Matrix (Fin (k a)) (Fin q) ℝ) (i : Fin (k a)) (j : Fin q) :
    (cavityGroupFrame k e a * A) (e ⟨a, i⟩) j = A i j := by
  simp [Matrix.mul_apply, cavityGroupFrame, e.injective.eq_iff]

lemma cavityGroupFrame_gram {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N) (a : Fin m) :
    (cavityGroupFrame k e a).transpose * cavityGroupFrame k e a = 1 := by
  ext i j
  change (∑ t : Fin N, (if t = e ⟨a, i⟩ then (1 : ℝ) else 0) *
    (if t = e ⟨a, j⟩ then (1 : ℝ) else 0)) = if i = j then 1 else 0
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]

lemma cavityGroupRotation_frame {N m : ℕ} (k : Fin m → ℕ)
    (e : ((a : Fin m) × Fin (k a)) ≃ Fin N)
    (U : (a : Fin m) → Orthogonal (k a)) (a : Fin m) :
    (cavityGroupRotation k e U : Matrix (Fin N) (Fin N) ℝ) * cavityGroupFrame k e a =
      cavityGroupFrame k e a * (U a : Matrix (Fin (k a)) (Fin (k a)) ℝ) := by
  ext i j
  obtain ⟨⟨b, l⟩, rfl⟩ := e.surjective i
  by_cases hba : b = a
  · subst b
    simp [Matrix.mul_apply, cavityGroupFrame, cavityGroupRotation,
      Matrix.submatrix_apply, e.injective.eq_iff, Matrix.blockDiagonal'_apply_eq]
  · have hne : ∀ t : Fin (k a), e ⟨b, l⟩ ≠ e ⟨a, t⟩ := by
      intro t ht
      exact hba (congrArg Sigma.fst (e.injective ht))
    simp [Matrix.mul_apply, cavityGroupFrame, cavityGroupRotation,
      Matrix.submatrix_apply, hne]
    exact Matrix.blockDiagonal'_apply_ne
      (fun c : Fin m => (U c : Matrix (Fin (k c)) (Fin (k c)) ℝ)) l j hba

end InvariantIsing

end

end OAI
