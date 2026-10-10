import OAI.Probability.InvariantIsing.Cavity.CavitySpectralStack

namespace OAI

/-! The special/cavity block matrix and its continuous limit. -/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def cavitySpecialBlocks {r d n : ℕ} (D : Matrix (Fin r) (Fin r) ℝ)
    (B : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ) :
    Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ :=
  Matrix.fromBlocks (B.transpose * D * B) (B.transpose * D * E)
    (E.transpose * D * B) (E.transpose * D * E)

lemma continuous_cavitySpecialBlocks {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) :
    Continuous (fun p : Matrix (Fin r) (Fin d) ℝ × Matrix (Fin r) (Fin n) ℝ =>
      cavitySpecialBlocks D p.1 p.2) := by
  apply Continuous.matrix_fromBlocks
  · exact (continuous_fst.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_fst
  · exact (continuous_fst.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_snd
  · exact (continuous_snd.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_fst
  · exact (continuous_snd.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_snd

theorem cavitySpecialBlocks_tendsto {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ)
    (E : ℕ → Matrix (Fin r) (Fin n) ℝ) (E₀ : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hEB : E₀.transpose * B₀ = 0) (hE : Tendsto E atTop (𝓝 E₀)) :
    Tendsto (fun k => cavitySpecialBlocks D (cavityComplement (E k) B₀) (E k))
      atTop (𝓝 (cavitySpecialBlocks D B₀ E₀)) := by
  have hB := cavityComplement_tendsto E E₀ B₀ hB₀ hEB hE
  have ht := (continuous_cavitySpecialBlocks D).tendsto (B₀, E₀) |>.comp (hB.prodMk_nhds hE)
  simpa only [Function.comp_def] using ht

def cavityLimitingStack {m n : ℕ} (ρ : Fin m → ℝ) :
    Matrix (Fin (m * n)) (Fin n) ℝ := fun i j =>
  Real.sqrt (ρ (finProdFinEquiv.symm i).1) *
    (if (finProdFinEquiv.symm i).2 = j then 1 else 0)

def cavityRepeatedSpectrum {m n : ℕ} (lam : Fin m → ℝ) :
    Matrix (Fin (m * n)) (Fin (m * n)) ℝ :=
  Matrix.diagonal (fun i => lam (finProdFinEquiv.symm i).1)

theorem cavityLimitingStack_gram {m n : ℕ} (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1) :
    (cavityLimitingStack (n := n) ρ).transpose * cavityLimitingStack (n := n) ρ =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have he : cavityLimitingStack (n := n) ρ =
      cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    ext i j
    simp only [cavityLimitingStack, cavitySpectralStack,
      cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [he, cavitySpectralStack_gram _ (fun a => Matrix.PosSemidef.one.smul (hρ a)),
    ← Finset.sum_smul, hsum, one_smul]

theorem cavityLimitingStack_cavity_block {m n : ℕ} (ρ lam : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) :
    (cavityLimitingStack (n := n) ρ).transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) ρ = (∑ a, ρ a * lam a) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  change (∑ k : Fin (m * n), (∑ t : Fin (m * n),
    cavityLimitingStack (n := n) ρ t i *
      (if t = k then lam (finProdFinEquiv.symm t).1 else 0)) *
      cavityLimitingStack (n := n) ρ k j) = _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [cavityLimitingStack, Equiv.symm_apply_apply]
  change (∑ a : Fin m, ∑ b : Fin n,
    Real.sqrt (ρ a) * (if b = i then 1 else 0) * lam a *
      (Real.sqrt (ρ a) * (if b = j then 1 else 0))) =
    (∑ a, ρ a * lam a) * (if i = j then 1 else 0)
  have hs (a : Fin m) :
      (∑ b : Fin n, Real.sqrt (ρ a) * (if b = i then 1 else 0) * lam a *
        (Real.sqrt (ρ a) * (if b = j then 1 else 0))) =
      (ρ a * lam a) * (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst j
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [mul_right_comm, Real.mul_self_sqrt (hρ a)]
    · have hji : j ≠ i := Ne.symm hij
      simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
      simp [hij, hji]
  simp_rw [hs]
  exact (Finset.sum_mul _ _ _).symm

end InvariantIsing

end

end OAI
