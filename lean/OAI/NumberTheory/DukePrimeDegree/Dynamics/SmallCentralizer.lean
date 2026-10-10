import OAI.NumberTheory.DukePrimeDegree.Dynamics.CentralizerContraction

namespace OAI

/-!
# Compact balls in a root centralizer

The diagonal with weights 1, -1, and 0 contracts the centralizer of the
corresponding root in reverse time. In particular, it preserves each
closed matrix ball in that centralizer. These compact sets give measurable
sets of small returns in the proof of EKL (2006), Lemma 4.2.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Elementwise

namespace DukePrimeDegree
open PrimeDegreePackets

def matrixClosedBall (n : ℕ) (r : ℝ) : Set (G n) :=
  (fun g : G n => g.val) ⁻¹' Metric.closedBall 1 r

lemma isCompact_matrixClosedBall (n : ℕ) (r : ℝ) : IsCompact (matrixClosedBall n r) :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage (isCompact_closedBall _ _)

lemma mem_matrixClosedBall_iff {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (g : G n) :
    g ∈ matrixClosedBall n r ↔ ∀ a b, |g.val a b - (1 : Matrix (Fin n) (Fin n) ℝ) a b| ≤ r := by
  change dist g.val 1 ≤ r ↔ _
  rw [dist_eq_norm, Matrix.norm_le_iff hr]
  simp only [Matrix.sub_apply, Real.norm_eq_abs]

lemma matrixClosedBall_subset_matrixBall {n : ℕ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) : matrixClosedBall n r ⊆ matrixBall n R := by
  intro g hg a b
  exact lt_of_le_of_lt ((mem_matrixClosedBall_iff hr g).mp hg a b) hrR

lemma entry_bound_of_mem_matrixClosedBall {n : ℕ} {r : ℝ}
    (hr : 0 ≤ r) {g : G n} (hg : g ∈ matrixClosedBall n r) (a b : Fin n) :
    |g.val a b| ≤ r + 1 := by
  have h := (mem_matrixClosedBall_iff hr g).mp hg a b
  by_cases hab : a = b
  · subst b
    rw [Matrix.one_apply_eq] at h
    obtain ⟨hl, hu⟩ := abs_le.mp h
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [Matrix.one_apply_ne hab, sub_zero] at h
    linarith

def rootContractionWeights {n : ℕ} (i j : Fin n) (r : Fin n) : ℝ :=
  (if r = i then 1 else 0) - (if r = j then 1 else 0)

lemma rootContractionWeights_sum {n : ℕ} (i j : Fin n) :
    ∑ r, rootContractionWeights i j r = 0 := by
  simp [rootContractionWeights, Finset.sum_sub_distrib]

lemma rootContractionWeights_gap {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    rootContractionWeights i j j < rootContractionWeights i j i := by
  simp [rootContractionWeights, hij, Ne.symm hij]

lemma rootContractionWeights_middle {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {r : Fin n} (hri : r ≠ i) (hrj : r ≠ j) :
    rootContractionWeights i j j < rootContractionWeights i j r ∧
      rootContractionWeights i j r < rootContractionWeights i j i := by
  simp [rootContractionWeights, hij, Ne.symm hij, hri, hrj]

lemma rootContractionWeights_entry_nonneg {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n)
    (hg : g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g)
    {r s : Fin n} (hentry : g.val r s ≠ 0) :
    0 ≤ rootContractionWeights i j r - rootContractionWeights i j s := by
  obtain ⟨hcol, hrow, _⟩ := (commutes_root_one_iff hij g).mp hg
  by_cases hrj : r = j
  · subst r
    have hsj : s = j := by
      by_contra h
      exact hentry (hrow s h)
    subst s
    simp
  by_cases hsi : s = i
  · subst s
    have hri : r = i := by
      by_contra h
      exact hentry (hcol r h)
    subst r
    simp
  by_cases hri : r = i <;> by_cases hsj : s = j
  all_goals norm_num [rootContractionWeights, hrj, hsi, hri, hsj, hij, Ne.symm hij]

lemma rootCentralizer_conjugate {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0) (t : ℝ)
    (g : G n)
    (hg : g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g) :
    let h := diagonalOneParameter ell hell t * g * diagonalOneParameter ell hell (-t)
    h * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * h := by
  dsimp only
  apply (commutes_root_one_iff hij _).mpr
  obtain ⟨hc, hr, hd⟩ := (commutes_root_one_iff hij g).mp hg
  refine ⟨?_, ?_, ?_⟩
  · intro r hri
    simp only [conjugation_entry, hc r hri, mul_zero]
  · intro s hsj
    simp only [conjugation_entry, hr s hsj, mul_zero]
  · simp only [conjugation_entry, sub_self, zero_mul, Real.exp_zero, one_mul, hd]

/-- Reverse diagonal time preserves the closed ball in the single-root
centralizer, because every allowed off-diagonal entry contracts. -/
theorem rootCentralizer_conjugate_mem_closedBall {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {r : ℝ} (hr : 0 ≤ r) (g : G n) (hgball : g ∈ matrixClosedBall n r)
    (hg : g * Matrix.SpecialLinearGroup.transvection hij 1 =
      Matrix.SpecialLinearGroup.transvection hij 1 * g) (t : ℝ) (ht : 0 ≤ t) :
    diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) (-t) * g *
      diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t ∈
        matrixClosedBall n r := by
  rw [mem_matrixClosedBall_iff hr] at hgball ⊢
  intro a b
  have he := conjugation_entry (rootContractionWeights i j)
    (rootContractionWeights_sum i j) g (-t) a b
  rw [neg_neg] at he
  rw [he]
  by_cases hab : a = b
  · subst b
    simpa only [sub_self, zero_mul, Real.exp_zero, one_mul] using hgball a a
  rw [Matrix.one_apply_ne hab, sub_zero]
  by_cases hg0 : g.val a b = 0
  · simp [hg0, hr]
  have hw := rootContractionWeights_entry_nonneg hij g hg hg0
  have hc : Real.exp ((rootContractionWeights i j a - rootContractionWeights i j b) * -t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hw (neg_nonpos.mpr ht))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ 1 * |g.val a b| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ ≤ r := by simpa only [one_mul, Matrix.one_apply_ne hab, sub_zero] using hgball a b

end DukePrimeDegree

end

end OAI
