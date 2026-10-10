import OAI.Probability.InvariantIsing.Cavity.CavityCompressionFactors
import OAI.Probability.InvariantIsing.Cavity.CavitySpecialPythagoras

namespace OAI

/-! The limiting frame extracted from the concrete compression has the
orthogonality and completeness used in the finite spectral cavity model. -/

noncomputable section
open Filter
open scoped Matrix Topology

namespace InvariantIsing

def cavityCompressionLimitFrame {m n d : ℕ} (e : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) : Matrix (Fin (m*n)) (Fin d) ℝ :=
  fun i j => B₀ (e i) j

lemma cavitySpectralStack_scalar_eq {m n : ℕ} (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) :
    cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      cavityLimitingStack (n := n) ρ := by
  ext i j
  simp only [cavitySpectralStack, cavityLimitingStack,
    cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]

lemma cavityCompressionLimitFrame_gram {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (hB₀ : B₀.transpose * B₀ = 1) :
    (cavityCompressionLimitFrame e B₀).transpose * cavityCompressionLimitFrame e B₀ = 1 := by
  ext i j
  have he := Equiv.sum_comp e (fun k => B₀ k i * B₀ k j)
  exact he.trans (congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) hB₀)

lemma cavityCompressionLimitFrame_perp {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (hEB : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0) :
    (cavityCompressionLimitFrame e B₀).transpose * cavityLimitingStack (n := n) ρ = 0 := by
  have ht := congrArg Matrix.transpose hEB
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at ht
  rw [← cavitySpectralStack_scalar_eq ρ hρ]
  ext i j
  have he := Equiv.sum_comp e (fun k => B₀ k i *
    cavitySpectralStack (fun a => ρ a • (1 : Matrix (Fin n) (Fin n) ℝ)) (e.symm k) j)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, cavityCompressionLimitFrame,
    Equiv.symm_apply_apply, cavityReindexedStack, Matrix.zero_apply] using
      he.trans (congrArg (fun A : Matrix (Fin d) (Fin n) ℝ => A i j) ht)

theorem cavityCompressionLimitFrame_complete {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1)
    (hEB : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0) :
    cavityCompressionLimitFrame e B₀ * (cavityCompressionLimitFrame e B₀).transpose +
      cavityLimitingStack (n := n) ρ * (cavityLimitingStack (n := n) ρ).transpose = 1 :=
  cavity_complement_projection_reindex e _ _ (cavityCompressionLimitFrame_gram e B₀ hB₀)
    (cavityLimitingStack_gram ρ hρ hsum) (cavityCompressionLimitFrame_perp e B₀ ρ hρ hEB)

end InvariantIsing

end

end OAI
