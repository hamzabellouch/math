import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRows

namespace OAI

/-! Eventual nondegeneracy of the Gaussian Gram matrix used to construct
fresh orthonormal directions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix

namespace InvariantIsing

def cavityEmpiricalGram {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ)

lemma cavityEmpiricalGram_posSemidef {q : ℕ} (x : ℕ → Fin q → ℝ) (n : ℕ) :
    (cavityEmpiricalGram x n).PosSemidef := by
  have he : cavityEmpiricalGram x n =
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, Matrix.vecMulVec (x k) (x k) := by
    ext i j
    simp only [cavityEmpiricalGram, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he]
  apply (Matrix.posSemidef_sum (Finset.range n) (fun k _ => ?_)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg n))
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (x k)

lemma cavity_posDef_of_posSemidef_det_ne_zero {q : ℕ}
    {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef) (hdet : G.det ≠ 0) :
    G.PosDef := by
  apply hG.1.posDef_iff_eigenvalues_pos.mpr
  intro i
  have hprod : (∏ j, hG.1.eigenvalues j) ≠ 0 := by
    rw [hG.1.det_eq_prod_eigenvalues] at hdet
    exact hdet
  have hi : hG.1.eigenvalues i ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hG.eigenvalues_nonneg i) hi.symm

lemma cavityEmpiricalGram_tendsto (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (cavityEmpiricalGram x) atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) :=
  cavityGaussianRows_gram_tendsto q

/-- Almost every Gaussian row sequence yields nondegenerate Gram matrices
at all sufficiently large sample sizes. -/
theorem cavityEmpiricalGram_eventually_posDef (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q, ∀ᶠ n in atTop, (cavityEmpiricalGram x n).PosDef := by
  filter_upwards [cavityEmpiricalGram_tendsto q] with x hx
  have hdet : Tendsto (fun n => (cavityEmpiricalGram x n).det) atTop (𝓝 (1 : ℝ)) := by
    have hd : Continuous (fun G : Matrix (Fin q) (Fin q) ℝ => G.det) :=
      continuous_id.matrix_det
    have ht := (hd.tendsto (1 : Matrix (Fin q) (Fin q) ℝ)).comp hx
    change Tendsto (fun n => (cavityEmpiricalGram x n).det) atTop
      (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ).det) at ht
    simpa only [Matrix.det_one] using ht
  filter_upwards [hdet.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  exact cavity_posDef_of_posSemidef_det_ne_zero (cavityEmpiricalGram_posSemidef x n)
    (ne_of_gt (show 0 < (cavityEmpiricalGram x n).det from hn))

end InvariantIsing

end

end OAI
