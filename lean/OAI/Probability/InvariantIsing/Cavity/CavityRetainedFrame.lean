import OAI.Probability.InvariantIsing.Cavity.CavitySpectralImages

namespace OAI

/-! Complete the cavity directions inside each spectral group. The added
columns are retained eigenvectors supported in the same group. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityGroupLift {r m q t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q) (B : Matrix (Fin q) (Fin t) ℝ) :
    Matrix (Fin r) (Fin t) ℝ :=
  fun i j => if hi : g i = a then B (e ⟨i, hi⟩) j else 0

lemma cavityGroupLift_support {r m q t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q) (B : Matrix (Fin q) (Fin t) ℝ)
    (i : Fin r) (hi : g i ≠ a) (j : Fin t) : cavityGroupLift g a e B i j = 0 := by
  simp only [cavityGroupLift, hi, dite_false]

lemma cavityGroupLift_gram {r m q s t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q)
    (B : Matrix (Fin q) (Fin s) ℝ) (C : Matrix (Fin q) (Fin t) ℝ) :
    (cavityGroupLift g a e B).transpose * cavityGroupLift g a e C = B.transpose * C := by
  classical
  ext i j
  change (∑ k : Fin r, cavityGroupLift g a e B k i * cavityGroupLift g a e C k j) =
    ∑ k : Fin q, B k i * C k j
  calc
    _ = ∑ k : {k : Fin r // g k = a}, B (e k) i * C (e k) j := by
      apply Finset.sum_congr_set {k : Fin r | g k = a}
      · intro k hk
        change g k = a at hk
        simp only [cavityGroupLift, hk, dite_true]
      · intro k hk
        change g k ≠ a at hk
        simp only [cavityGroupLift, hk, dite_false, zero_mul]
    _ = _ := Equiv.sum_comp e (fun k : Fin q => B k i * C k j)

lemma cavityGroupLift_restrict {r m q t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q) (W : Matrix (Fin r) (Fin t) ℝ)
    (hW : ∀ i, g i ≠ a → ∀ j, W i j = 0) :
    cavityGroupLift g a e (fun i j => W (e.symm i) j) = W := by
  ext i j
  by_cases hi : g i = a
  · simp only [cavityGroupLift, hi, dite_true, Equiv.symm_apply_apply]
  · simp only [cavityGroupLift, hi, dite_false, hW i hi j]

lemma cavityNormalizeFrame_spectral_support {r m n : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m)
    (i : Fin r) (hi : g i ≠ a) (j : Fin n) :
    cavityNormalizeFrame (cavitySpectralImage g A a) i j = 0 := by
  change (∑ k : Fin n, cavitySpectralImage g A a i k * _) = 0
  apply Finset.sum_eq_zero
  intro k _
  simp only [cavitySpectralImage, hi, ite_false, zero_mul]

lemma cavity_complement_projection {k n : ℕ}
    (B : Matrix (Fin (k + n)) (Fin k) ℝ) (Y : Matrix (Fin (k + n)) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hY : Y.transpose * Y = 1)
    (hYB : Y.transpose * B = 0) :
    B * B.transpose + Y * Y.transpose = 1 := by
  have hBY : B.transpose * Y = 0 := by
    have h := congrArg Matrix.transpose hYB
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : (Matrix.fromCols B Y).transpose * Matrix.fromCols B Y = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols, hB, hBY, hYB, hY,
      Matrix.fromBlocks_one]
  have h := (Matrix.mul_eq_one_comm_of_equiv
    (finSumFinEquiv : Fin k ⊕ Fin n ≃ Fin (k + n))).mp hQ
  simpa only [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using h

lemma cavityGroupLift_projection {r m q s t : ℕ} (g : Fin r → Fin m) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin q)
    (B : Matrix (Fin q) (Fin s) ℝ) (C : Matrix (Fin q) (Fin t) ℝ)
    (hBC : B * B.transpose + C * C.transpose = 1) :
    cavityGroupLift g a e B * (cavityGroupLift g a e B).transpose +
      cavityGroupLift g a e C * (cavityGroupLift g a e C).transpose =
        Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) := by
  classical
  ext i j
  by_cases hi : g i = a <;> by_cases hj : g j = a
  · have h := congrArg (fun M : Matrix (Fin q) (Fin q) ℝ =>
      M (e ⟨i, hi⟩) (e ⟨j, hj⟩)) hBC
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, Matrix.one_apply, Equiv.apply_eq_iff_eq,
      Subtype.mk.injEq, Matrix.diagonal_apply, ite_true] using h
  · have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, dite_false, mul_zero, Finset.sum_const_zero,
      add_zero, Matrix.diagonal_apply_ne _ hij]
  · have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_true, dite_false, zero_mul, Finset.sum_const_zero,
      add_zero, Matrix.diagonal_apply_ne _ hij]
  · simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      cavityGroupLift, hi, hj, dite_false, zero_mul, Finset.sum_const_zero, add_zero]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, hi, ite_false]
    · rw [Matrix.diagonal_apply_ne _ hij]

theorem cavityRetainedFrame_exists {r m n k : ℕ}
    (g : Fin r → Fin m) (A : Matrix (Fin r) (Fin n) ℝ) (a : Fin m)
    (e : {i : Fin r // g i = a} ≃ Fin (k + n))
    (hA : ((cavitySpectralImage g A a).transpose * cavitySpectralImage g A a).PosDef) :
    ∃ R : Matrix (Fin r) (Fin k) ℝ,
      R.transpose * R = 1 ∧
      (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose * R = 0 ∧
      (∀ i, g i ≠ a → ∀ j, R i j = 0) ∧
      R * R.transpose + cavityNormalizeFrame (cavitySpectralImage g A a) *
        (cavityNormalizeFrame (cavitySpectralImage g A a)).transpose =
          Matrix.diagonal (fun i => if g i = a then (1 : ℝ) else 0) := by
  let W := cavityNormalizeFrame (cavitySpectralImage g A a)
  let Y : Matrix (Fin (k + n)) (Fin n) ℝ := fun i j => W (e.symm i) j
  have hW : cavityGroupLift g a e Y = W :=
    cavityGroupLift_restrict g a e W (cavityNormalizeFrame_spectral_support g A a)
  have hY : Y.transpose * Y = 1 := by
    rw [← cavityGroupLift_gram g a e Y Y, hW]
    exact cavityNormalizeFrame_gram _ hA
  obtain ⟨B, hB, hYB⟩ := cavity_frame_completion Y hY
  refine ⟨cavityGroupLift g a e B, ?_, ?_, ?_, ?_⟩
  · rw [cavityGroupLift_gram, hB]
  · change W.transpose * cavityGroupLift g a e B = 0
    rw [← hW, cavityGroupLift_gram, hYB]
  · exact cavityGroupLift_support g a e B
  · change _ + W * W.transpose = _
    rw [← hW]
    exact cavityGroupLift_projection g a e B Y (cavity_complement_projection B Y hB hY hYB)

lemma cavitySpectralSupport_crossGram {r m s t : ℕ}
    (g : Fin r → Fin m) (a b : Fin m) (hab : a ≠ b)
    (V : Matrix (Fin r) (Fin s) ℝ) (W : Matrix (Fin r) (Fin t) ℝ)
    (hV : ∀ i, g i ≠ a → ∀ j, V i j = 0)
    (hW : ∀ i, g i ≠ b → ∀ j, W i j = 0) : V.transpose * W = 0 := by
  ext i j
  change (∑ k, V k i * W k j) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases ha : g k = a
  · have hb : g k ≠ b := fun h => hab (ha.symm.trans h)
    rw [hW k hb j, mul_zero]
  · rw [hV k ha i, zero_mul]

lemma cavitySpectralSupport_eigen {r m t : ℕ}
    (g : Fin r → Fin m) (a : Fin m) (lam : Fin m → ℝ)
    (V : Matrix (Fin r) (Fin t) ℝ)
    (hV : ∀ i, g i ≠ a → ∀ j, V i j = 0) :
    Matrix.diagonal (fun i => lam (g i)) * V = lam a • V := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.smul_apply]
  by_cases hi : g i = a
  · rw [hi]; rfl
  · rw [hV i hi j, mul_zero, smul_zero]

lemma cavitySpectralProjectors_sum {r m : ℕ} (g : Fin r → Fin m) :
    (∑ a, Matrix.diagonal (fun i : Fin r => if g i = a then (1 : ℝ) else 0)) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Matrix.one_apply_eq]
  · simp only [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hij,
      Finset.sum_const_zero, Matrix.one_apply_ne hij]

end InvariantIsing

end

end OAI
