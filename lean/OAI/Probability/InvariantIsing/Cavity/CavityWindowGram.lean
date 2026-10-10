import OAI.Probability.InvariantIsing.Cavity.CavityHaarProjection

namespace OAI

/-! Gaussian Gram matrices compressed to a growing spectral coordinate
window. Prefix differences avoid introducing a second Gaussian array. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def cavityPrefixGram {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) (l : ℕ) :
    Matrix (Fin q) (Fin q) ℝ :=
  A.transpose * Matrix.diagonal (fun i : Fin N => if i.val < l then (1 : ℝ) else 0) * A

lemma continuous_cavityPrefixGram (N q l : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin q) ℝ => cavityPrefixGram A l) :=
  (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_id

lemma cavityPrefixGram_apply {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (l : ℕ) (i j : Fin q) :
    cavityPrefixGram A l i j = ∑ k : Fin N, if k.val < l then A k i * A k j else 0 := by
  change (∑ k : Fin N, (∑ t : Fin N,
    A t i * (if t = k then (if t.val < l then (1 : ℝ) else 0) else 0)) * A k j) = _
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all

lemma cavityPrefixGram_mul {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (C : Matrix (Fin q) (Fin q) ℝ) (l : ℕ) :
    cavityPrefixGram (A * C) l = C.transpose * cavityPrefixGram A l * C := by
  simp only [cavityPrefixGram, Matrix.transpose_mul, Matrix.mul_assoc]

lemma cavityPrefixGram_gaussian {q : ℕ} (x : ℕ → Fin q → ℝ)
    (N l : ℕ) (hl : l ≤ N) :
    cavityPrefixGram (cavityGaussianMatrix x N) l =
      ((l : ℝ) / N) • cavityEmpiricalGram x l := by
  ext i j
  rw [cavityPrefixGram_apply]
  simp only [cavityGaussianMatrix, div_mul_div_comm,
    Real.mul_self_sqrt (Nat.cast_nonneg N)]
  have hsum : (∑ k : Fin N, if k.val < l then x k i * x k j / N else 0) =
      (∑ k ∈ Finset.range l, x k i * x k j) / N := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if k < l then x k i * x k j / N else 0) N]
    rw [← Finset.sum_filter]
    have hs : (Finset.range N).filter (fun k => k < l) = Finset.range l := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hs, Finset.sum_div]
  rw [hsum]
  simp only [Matrix.smul_apply, cavityEmpiricalGram, smul_eq_mul]
  by_cases hzero : l = 0
  · subst l
    simp
  · have hnz : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hzero
    field_simp

open scoped MatrixOrder Matrix.Norms.L2Operator in
lemma cavityPrefixGram_normalized {q : ℕ} (x : ℕ → Fin q → ℝ)
    (N l : ℕ) (hl : l ≤ N) :
    cavityPrefixGram (cavityNormalizeFrame (cavityGaussianMatrix x N)) l =
      ((CFC.sqrt (cavityEmpiricalGram x N))⁻¹).transpose *
        (((l : ℝ) / N) • cavityEmpiricalGram x l) *
        (CFC.sqrt (cavityEmpiricalGram x N))⁻¹ := by
  rw [cavityNormalizeFrame, cavityGaussianMatrix_gram, cavityPrefixGram_mul,
    cavityPrefixGram_gaussian x N l hl]

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem cavityPrefixGram_tendsto {q : ℕ} (x : ℕ → Fin q → ℝ)
    (hx : Tendsto (cavityEmpiricalGram x) atTop (𝓝 1))
    (N l : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hl : Tendsto l atTop atTop)
    (hle : ∀ k, l k ≤ N k) (ρ : ℝ)
    (hρ : Tendsto (fun k => (l k : ℝ) / N k) atTop (𝓝 ρ)) :
    Tendsto (fun k => cavityPrefixGram
      (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k))
      atTop (𝓝 (ρ • (1 : Matrix (Fin q) (Fin q) ℝ))) := by
  have hG := hρ.smul (hx.comp hl)
  have hC := (cavity_gram_correction_tendsto (cavityEmpiricalGram x)
    (cavityEmpiricalGram_posSemidef x) hx).comp hN
  have hc : Continuous (fun p : Matrix (Fin q) (Fin q) ℝ × Matrix (Fin q) (Fin q) ℝ =>
      p.2.transpose * p.1 * p.2) :=
    (continuous_snd.matrix_transpose.matrix_mul continuous_fst).matrix_mul continuous_snd
  have ht := hc.tendsto (ρ • 1, 1) |>.comp (hG.prodMk_nhds hC)
  simpa only [Function.comp_def, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    ← cavityPrefixGram_normalized x _ _ (hle _)] using ht

lemma cavityPrefixGram_zero {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) :
    cavityPrefixGram A 0 = 0 := by
  ext i j
  simp only [cavityPrefixGram_apply, Nat.not_lt_zero, ite_false, Finset.sum_const_zero,
    Matrix.zero_apply]

def cavityWindowGram {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) (l u : ℕ) :
    Matrix (Fin q) (Fin q) ℝ := cavityPrefixGram A u - cavityPrefixGram A l

lemma continuous_cavityWindowGram (N q l u : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin q) ℝ => cavityWindowGram A l u) :=
  (continuous_cavityPrefixGram N q u).sub (continuous_cavityPrefixGram N q l)

lemma cavityWindowGram_posSemidef {N q : ℕ}
    (A : Matrix (Fin N) (Fin q) ℝ) (l u : ℕ) (hlu : l ≤ u) :
    (cavityWindowGram A l u).PosSemidef := by
  let D : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal
    (fun i : Fin N => if l ≤ i.val ∧ i.val < u then (1 : ℝ) else 0)
  have he : cavityWindowGram A l u = A.transpose * D * A := by
    have hd : Matrix.diagonal (fun i : Fin N => if i.val < u then (1 : ℝ) else 0) -
        Matrix.diagonal (fun i : Fin N => if i.val < l then (1 : ℝ) else 0) = D := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [D, Matrix.sub_apply, Matrix.diagonal_apply_eq]
        split_ifs <;> norm_num at * <;> omega
      · simp [D, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij]
    rw [cavityWindowGram, cavityPrefixGram, cavityPrefixGram,
      ← Matrix.sub_mul, ← Matrix.mul_sub, hd]
  rw [he]
  have hd : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    split_ifs <;> norm_num)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hd.conjTranspose_mul_mul_same A

lemma cavityPrefixGram_full {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ) :
    cavityPrefixGram A N = A.transpose * A := by
  have hd : Matrix.diagonal (fun i : Fin N => if i.val < N then (1 : ℝ) else 0) = 1 := by
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [cavityPrefixGram, hd, Matrix.mul_one]

lemma cavityWindowGram_partition {N q : ℕ} (A : Matrix (Fin N) (Fin q) ℝ)
    (m : ℕ) (c : ℕ → ℕ) (hc0 : c 0 = 0) (hcm : c m = N) :
    (∑ a ∈ Finset.range m, cavityWindowGram A (c a) (c (a + 1))) = A.transpose * A := by
  have ht := Finset.sum_range_sub (fun a => cavityPrefixGram A (c a)) m
  simpa only [cavityWindowGram, hcm, hc0, cavityPrefixGram_full,
    cavityPrefixGram_zero, sub_zero] using ht

theorem cavityWindowGram_tendsto_ae (q : ℕ)
    (N l u : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : Tendsto u atTop atTop) (hl : (∀ k, l k = 0) ∨ Tendsto l atTop atTop)
    (hle : ∀ k, l k ≤ N k) (hue : ∀ k, u k ≤ N k)
    (ρl ρu : ℝ)
    (hρl : Tendsto (fun k => (l k : ℝ) / N k) atTop (𝓝 ρl))
    (hρu : Tendsto (fun k => (u k : ℝ) / N k) atTop (𝓝 ρu)) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun k => cavityWindowGram
        (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k))
        atTop (𝓝 ((ρu - ρl) • (1 : Matrix (Fin q) (Fin q) ℝ))) := by
  filter_upwards [cavityEmpiricalGram_tendsto q] with x hx
  have hupper := cavityPrefixGram_tendsto x hx N u hN hu hue ρu hρu
  have hlower : Tendsto (fun k => cavityPrefixGram
      (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k))
      atTop (𝓝 (ρl • (1 : Matrix (Fin q) (Fin q) ℝ))) := by
    rcases hl with hz | hlt
    · have hr : ρl = 0 := by
        have he : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 ρl) := by
          simpa only [hz, Nat.cast_zero, zero_div] using hρl
        exact tendsto_nhds_unique he tendsto_const_nhds
      simpa only [hz, cavityPrefixGram_zero, hr, zero_smul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Matrix (Fin q) (Fin q) ℝ)) atTop (𝓝 0))
    · exact cavityPrefixGram_tendsto x hx N l hN hlt hle ρl hρl
  simpa only [cavityWindowGram, sub_smul] using hupper.sub hlower

end InvariantIsing

end

end OAI
