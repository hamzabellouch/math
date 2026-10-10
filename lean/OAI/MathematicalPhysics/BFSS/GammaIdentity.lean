import Mathlib
import OAI.MathematicalPhysics.BFSS.GammaWords

namespace OAI

/-! The spin identity from trace pairings with Clifford words. -/

namespace BFSSGamma
noncomputable section
open Matrix Finset
variable (G : Space → Mat)
variable (hG : ∀ i j, G i * G j + G j * G i = (if i = j then 2 else 0) • (1 : Mat))
include hG
variable (hSym : ∀ i, (G i).transpose = G i)
include hSym
omit hG hSym in
lemma dot_mulVec_left (A : Mat) (x y : Spin → ℝ) :
    dotProduct (A *ᵥ x) y = dotProduct x (A.transpose *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

omit hG hSym in
lemma dot_transpose (A : Mat) (v : Spin → ℝ) :
    dotProduct v (A.transpose *ᵥ v) = dotProduct v (A *ᵥ v) := by
  rw [← dot_mulVec_left, dotProduct_comm]

omit hG hSym in
lemma trace_mul_outer (M : Mat) (x y : Spin → ℝ) :
    Matrix.trace (M * Matrix.vecMulVec x y) = dotProduct y (M *ᵥ x) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

omit hG hSym in
lemma trace_symm_outer (M : Mat) (hM : M.transpose = M) (x y : Spin → ℝ) :
    Matrix.trace (M * symm (Matrix.vecMulVec x y)) = dotProduct y (M *ᵥ x) := by
  rw [symm, mul_smul_comm, mul_add, Matrix.trace_smul, Matrix.trace_add]
  have ht := Matrix.trace_transpose_mul M (Matrix.vecMulVec x y)
  rw [hM] at ht
  rw [ht, trace_mul_outer]
  simp only [smul_eq_mul]
  ring

omit hG hSym in
lemma trace_skew_symm (M B : Mat) (hM : M.transpose = -M) (hB : B.transpose = B) :
    Matrix.trace (M * B) = 0 := by
  have h := Matrix.trace_transpose_mul M B
  rw [hM, hB, neg_mul, Matrix.trace_neg] at h
  linarith

def spinLHS (v : Spin → ℝ) (j : Space) : Mat :=
  ∑ i, symm (Matrix.vecMulVec (G i *ᵥ v) (gammaTwo G i j *ᵥ v))

omit hG hSym in
lemma spinLHS_symmetric (v : Spin → ℝ) (j : Space) : (spinLHS G v j).transpose = spinLHS G v j := by
  simp only [spinLHS, Matrix.transpose_sum, symm_transpose]

lemma spin_trace_pair (M : Mat) (hM : M.transpose = M) (c : ℝ)
    (hc : ∑ i, G i * M * G i = c • M) (v : Spin → ℝ) (j : Space) :
    Matrix.trace (M * spinLHS G v j) = (c - 1) * dotProduct v ((M * G j) *ᵥ v) := by
  have hterm (i : Space) :
      Matrix.trace (M * symm (Matrix.vecMulVec (G i *ᵥ v) (gammaTwo G i j *ᵥ v))) =
      dotProduct v (((gammaTwo G i j).transpose * M * G i) *ᵥ v) := by
    rw [trace_symm_outer _ hM, dot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hsum : (∑ i, (gammaTwo G i j).transpose * M * G i) =
      G j * (∑ i, G i * M * G i) - M * G j := by
    simp_rw [gammaTwo_alt G hG, Matrix.transpose_sub, Matrix.transpose_mul, hSym,
      Matrix.transpose_smul, Matrix.transpose_one, sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · simp only [Matrix.mul_sum, Matrix.mul_assoc]
    · have hδ (i : Space) :
          ((if i = j then (1 : ℝ) else 0) • (1 : Mat)) * M * G i =
          if i = j then M * G j else 0 := by
        split_ifs with hij
        · subst i; simp
        · simp
      simp_rw [hδ]
      simp
  have hswap : dotProduct v ((G j * M) *ᵥ v) = dotProduct v ((M * G j) *ᵥ v) := by
    have h := dot_transpose (M * G j) v
    simpa only [Matrix.transpose_mul, hM, hSym] using h
  rw [spinLHS, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [hterm]
  rw [← dotProduct_sum, ← Matrix.sum_mulVec, hsum, hc, mul_smul_comm,
    Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, hswap]
  ring

omit hSym in
lemma trace_word (s : Finset Space) (hs : s.card ≤ 4) :
    Matrix.trace (word G s) = if s = ∅ then 16 else 0 := by
  have h := trace_reverseWord_word G hG (s := ∅) (by simp) hs
  simpa [reverseWord, eq_comm] using h

omit hG hSym in
lemma word_singleton
    (_hG : ∀ first second, G first * G second + G second * G first =
      (if first = second then 2 else 0) • (1 : Mat))
    (j : Space) : word G {j} = G j := by simp [word]

omit hSym in
lemma trace_word_gamma (s : Finset Space) (hs : s.card ≤ 4)
    (hrev : reverseWord G s = word G s) (j : Space) :
    Matrix.trace (word G s * G j) = if s = {j} then 16 else 0 := by
  have h := trace_reverseWord_word G hG hs (s := s) (t := {j}) (by simp)
  rw [hrev, word_singleton G hG] at h
  exact h

def spinRHS (v : Spin → ℝ) (j : Space) : Mat :=
  (1 / 2 * dotProduct v (G j *ᵥ v)) • (1 : Mat) - (1 / 2 : ℝ) • G j

omit hG in
lemma spinRHS_symmetric (v : Spin → ℝ) (j : Space) :
    (spinRHS G v j).transpose = spinRHS G v j := by
  simp only [spinRHS, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hSym]

omit hG hSym in
lemma trace_spinRHS (M : Mat) (v : Spin → ℝ) (j : Space) :
    Matrix.trace (M * spinRHS G v j) =
      (1 / 2 * dotProduct v (G j *ᵥ v)) * Matrix.trace M -
      (1 / 2 : ℝ) * Matrix.trace (M * G j) := by
  simp only [spinRHS, mul_sub, mul_smul_comm, mul_one, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul]

omit hG hSym in
lemma dot_skew_zero (M : Mat) (hM : M.transpose = -M) (v : Spin → ℝ) :
    dotProduct v (M *ᵥ v) = 0 := by
  have h := dot_transpose M v
  rw [hM, Matrix.neg_mulVec, dotProduct_neg] at h
  linarith

lemma dot_gamma_product (v : Spin → ℝ) (hv : ∑ α, v α ^ 2 = 1) (i j : Space) :
    dotProduct v ((G i * G j) *ᵥ v) = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst j
    rw [gamma_sq G hG, Matrix.one_mulVec]
    simpa only [dotProduct, pow_two] using hv
  · apply dot_skew_zero
    rw [Matrix.transpose_mul, hSym, hSym, gamma_anti G hG (Ne.symm hij)]

omit hSym in
lemma trace_gamma (j : Space) : Matrix.trace (G j) = 0 := by
  have h := trace_word G hG {j} (by simp)
  simpa only [word_singleton G hG, Finset.singleton_ne_empty, ite_false] using h

lemma spin_identity_trace_word (s : Finset Space) (hs : s.card ≤ 4)
    (v : Spin → ℝ) (hv : ∑ α, v α ^ 2 = 1) (j : Space) :
    Matrix.trace (word G s * spinLHS G v j) = Matrix.trace (word G s * spinRHS G v j) := by
  have htrans := word_transpose G hG hSym s
  have heigen := sum_word_conj G hG s
  interval_cases hcard : s.card
  · have hs0 : s = ∅ := Finset.card_eq_zero.mp hcard
    subst s
    have hM : (word G ∅).transpose = word G ∅ := by simp [word]
    have hE : ∑ i, G i * word G ∅ * G i = (9 : ℝ) • word G ∅ := by
      simpa using heigen
    rw [spin_trace_pair G hG hSym _ hM 9 hE, trace_spinRHS]
    simp only [word, Finset.sort_empty, List.map_nil, List.prod_nil, one_mul,
      Matrix.trace_one, Fintype.card_fin, trace_gamma G hG]
    norm_num [Spin]
    ring
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    have hE : ∑ k, G k * G i * G k = (-7 : ℝ) • G i := by
      norm_num [word_singleton G hG] at heigen
      simpa only [neg_smul] using heigen
    rw [word_singleton G hG, spin_trace_pair G hG hSym _ (hSym i) (-7) hE,
      trace_spinRHS, dot_gamma_product G hG hSym v hv, trace_gamma G hG]
    have ht : Matrix.trace (G i * G j) = if i = j then 16 else 0 := by
      have h := trace_reverseWord_word G hG (s := {i}) (t := {j}) (by simp) (by simp)
      simpa [reverseWord, word, Finset.singleton_inj] using h
    rw [ht]
    split_ifs <;> norm_num
  · have hM : (word G s).transpose = -word G s := by
      norm_num [hcard, rankSign, Nat.choose] at htrans
      exact htrans
    rw [trace_skew_symm _ _ hM (spinLHS_symmetric G v j),
      trace_skew_symm _ _ hM (spinRHS_symmetric G hSym v j)]
  · have hM : (word G s).transpose = -word G s := by
      norm_num [hcard, rankSign, Nat.choose] at htrans
      exact htrans
    rw [trace_skew_symm _ _ hM (spinLHS_symmetric G v j),
      trace_skew_symm _ _ hM (spinRHS_symmetric G hSym v j)]
  · have hM : (word G s).transpose = word G s := by
      norm_num [hcard, rankSign, Nat.choose] at htrans
      exact htrans
    have hE : ∑ i, G i * word G s * G i = (1 : ℝ) • word G s := by
      norm_num [hcard] at heigen
      simpa only [one_smul] using heigen
    have hrev : reverseWord G s = word G s := by
      rw [reverseWord, list_reverse_eq G hG _ (Finset.sort_nodup _ _), Finset.length_sort]
      norm_num [rankSign, hcard, Nat.choose]
      rfl
    have hs0 : s ≠ ∅ := by intro h; simp [h] at hcard
    have hsj : s ≠ {j} := by intro h; simp [h] at hcard
    rw [spin_trace_pair G hG hSym _ hM 1 hE, trace_spinRHS,
      trace_word G hG s (by omega), trace_word_gamma G hG s (by omega) hrev j,
      ite_eq_right hs0, ite_eq_right hsj]
    norm_num

theorem spinIdentity : SpinIdentity G := by
  intro v hv j
  change spinLHS G v j = spinRHS G v j
  apply matrix_eq_of_trace_words G hG
  intro a
  exact spin_identity_trace_word G hG hSym (shortSet a) (shortSet_card a) v hv j

end
end BFSSGamma

end OAI
