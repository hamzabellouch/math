import OAI.Probability.InvariantIsing.Cavity.CavityConcreteComplement
import OAI.Probability.InvariantIsing.Cavity.CavityContinuousCutoff

namespace OAI

/-! The actual cavity factor coefficients as functions of the compression
grams, with their limit at the deterministic scalar compression. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavitySmallFactorBlocks {s d n : ℕ}
    (D : Matrix (Fin s) (Fin s) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ) :
    CavityFactorBlocks d n :=
  (B.transpose * D * B - A₀, B.transpose * D * T, T.transpose * D * T)

lemma continuous_cavitySmallFactorBlocks {s d n : ℕ}
    (D : Matrix (Fin s) (Fin s) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun p : Matrix (Fin s) (Fin d) ℝ × Matrix (Fin s) (Fin n) ℝ =>
      cavitySmallFactorBlocks D A₀ p.1 p.2) := by
  exact (((continuous_fst.matrix_transpose.matrix_mul continuous_const).matrix_mul
    continuous_fst).sub continuous_const).prodMk
      (((continuous_fst.matrix_transpose.matrix_mul continuous_const).matrix_mul
        continuous_snd).prodMk
        ((continuous_snd.matrix_transpose.matrix_mul continuous_const).matrix_mul continuous_snd))

def cavityCompressionFactorBlocks {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) : CavityFactorBlocks d n :=
  cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam) (Matrix.diagonal lam₀)
    (cavityConcreteComplement e B₀ M) (cavitySpectralStack M)

lemma measurable_cavitySpectralStack (m n : ℕ) :
    Measurable (cavitySpectralStack :
      (Fin m → Matrix (Fin n) (Fin n) ℝ) → Matrix (Fin (m*n)) (Fin n) ℝ) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
    CFC.sqrt (M (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2 j)
  exact (CFC.measurable_sqrt.comp
    (measurable_pi_apply (finProdFinEquiv.symm i).1)).eval_matrix

lemma measurable_cavityCompressionFactorBlocks {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) :
    Measurable (cavityCompressionFactorBlocks e lam lam₀ B₀) := by
  have hB := measurable_cavityConcreteComplement e B₀
  have hT := measurable_cavitySpectralStack m n
  unfold cavityCompressionFactorBlocks cavitySmallFactorBlocks
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  all_goals
    apply Measurable.of_eval_matrix
    intro i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop

lemma cavitySpectralStack_scalar_tendsto {m n : ℕ}
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (M : ℕ → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ k a, (M k a).PosSemidef)
    (hlim : ∀ a, Tendsto (fun k => M k a) atTop (𝓝 (ρ a • 1))) :
    Tendsto (fun k => cavitySpectralStack (M k)) atTop
      (𝓝 (cavitySpectralStack (fun a => ρ a • 1))) := by
  have he : cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      fun i j => Real.sqrt (ρ (finProdFinEquiv.symm i).1) *
        (1 : Matrix (Fin n) (Fin n) ℝ) (finProdFinEquiv.symm i).2 j := by
    ext i j
    simp only [cavitySpectralStack, cavity_sqrt_scalar_identity _ (hρ _),
      Matrix.smul_apply, smul_eq_mul]
  rw [he]
  exact cavitySpectralStack_tendsto M ρ hρ hM hlim

theorem cavityConcreteComplement_tendsto {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (hperp : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0)
    (M : ℕ → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ k a, (M k a).PosSemidef)
    (hlim : ∀ a, Tendsto (fun k => M k a) atTop (𝓝 (ρ a • 1))) :
    Tendsto (fun k => cavityConcreteComplement e B₀ (M k)) atTop
      (𝓝 (fun i j => B₀ (e i) j)) := by
  have hS := cavitySpectralStack_scalar_tendsto ρ hρ M hM hlim
  have hE : Tendsto (fun k => cavityReindexedStack e (M k)) atTop
      (𝓝 (cavityReindexedStack e (fun a => ρ a • 1))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mpr fun j =>
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hS (e.symm i)) j
  have hC := cavitySelectedComplement_tendsto _ _ B₀ hB₀ hperp hE
  apply tendsto_pi_nhds.mpr
  intro i
  exact tendsto_pi_nhds.mpr fun j =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hC (e i)) j

theorem cavityCompressionFactorBlocks_tendsto {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (hperp : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0)
    (M : ℕ → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ k a, (M k a).PosSemidef)
    (hlim : ∀ a, Tendsto (fun k => M k a) atTop (𝓝 (ρ a • 1))) :
    Tendsto (fun k => cavityCompressionFactorBlocks e lam lam₀ B₀ (M k)) atTop
      (𝓝 (cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
        (Matrix.diagonal lam₀) (fun i j => B₀ (e i) j)
        (cavitySpectralStack (fun a => ρ a • 1)))) := by
  have hB := cavityConcreteComplement_tendsto e B₀ hB₀ ρ hρ hperp M hM hlim
  have hT := cavitySpectralStack_scalar_tendsto ρ hρ M hM hlim
  have hc := (continuous_cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
    (Matrix.diagonal lam₀)).tendsto
      ((fun i j => B₀ (e i) j), cavitySpectralStack (fun a => ρ a • 1))
  simpa only [Function.comp_def, cavityCompressionFactorBlocks] using
    hc.comp (hB.prodMk_nhds hT)

end InvariantIsing

end

end OAI
