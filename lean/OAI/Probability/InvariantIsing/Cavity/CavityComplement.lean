import OAI.Probability.InvariantIsing.Cavity.CavityFrameLimit

namespace OAI

/-! A continuous local choice of the special complement in the cavity
block: project a limiting frame and orthonormalize its columns. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavityNormalizeFrame_tendsto {r d : ℕ}
    (B : ℕ → Matrix (Fin r) (Fin d) ℝ) (B₀ : Matrix (Fin r) (Fin d) ℝ)
    (hB₀ : B₀.transpose * B₀ = 1) (hB : Tendsto B atTop (𝓝 B₀)) :
    Tendsto (fun k => cavityNormalizeFrame (B k)) atTop (𝓝 B₀) := by
  have hGram : Tendsto (fun k => (B k).transpose * B k) atTop
      (𝓝 (1 : Matrix (Fin d) (Fin d) ℝ)) := by
    have hc : Continuous (fun A : Matrix (Fin r) (Fin d) ℝ => A.transpose * A) :=
      continuous_id.matrix_transpose.matrix_mul continuous_id
    simpa only [Function.comp_def, hB₀] using hc.tendsto B₀ |>.comp hB
  have hInv := cavity_gram_correction_tendsto (fun k => (B k).transpose * B k)
    (fun k => by simpa using Matrix.posSemidef_conjTranspose_mul_self (B k)) hGram
  have hc : Continuous (fun p : Matrix (Fin r) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ =>
      p.1 * p.2) := continuous_fst.matrix_mul continuous_snd
  simpa only [Function.comp_def, Matrix.mul_one, cavityNormalizeFrame] using
    hc.tendsto (B₀, 1) |>.comp (hB.prodMk_nhds hInv)

def cavityRawComplement {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) : Matrix (Fin r) (Fin d) ℝ :=
  (1 - E * E.transpose) * B₀

lemma cavityRawComplement_eq {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hEB : E.transpose * B₀ = 0) :
    cavityRawComplement E B₀ = B₀ := by
  simp only [cavityRawComplement, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, hEB, Matrix.mul_zero, sub_zero]

lemma cavityRawComplement_orthogonal {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hE : E.transpose * E = 1) :
    E.transpose * cavityRawComplement E B₀ = 0 := by
  simp only [cavityRawComplement, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_sub, ← Matrix.mul_assoc, hE, Matrix.one_mul, sub_self]

def cavityComplement {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) : Matrix (Fin r) (Fin d) ℝ :=
  cavityNormalizeFrame (cavityRawComplement E B₀)

lemma cavityComplement_orthogonal {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hE : E.transpose * E = 1) :
    E.transpose * cavityComplement E B₀ = 0 := by
  rw [cavityComplement, cavityNormalizeFrame, ← Matrix.mul_assoc,
    cavityRawComplement_orthogonal E B₀ hE, Matrix.zero_mul]

lemma cavityComplement_gram {r n d : ℕ} (E : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ)
    (hG : ((cavityRawComplement E B₀).transpose * cavityRawComplement E B₀).PosDef) :
    (cavityComplement E B₀).transpose * cavityComplement E B₀ = 1 :=
  cavityNormalizeFrame_gram _ hG

theorem cavityComplement_tendsto {r n d : ℕ}
    (E : ℕ → Matrix (Fin r) (Fin n) ℝ) (E₀ : Matrix (Fin r) (Fin n) ℝ)
    (B₀ : Matrix (Fin r) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hEB : E₀.transpose * B₀ = 0) (hE : Tendsto E atTop (𝓝 E₀)) :
    Tendsto (fun k => cavityComplement (E k) B₀) atTop (𝓝 B₀) := by
  apply cavityNormalizeFrame_tendsto _ B₀ hB₀
  have hc : Continuous (fun A : Matrix (Fin r) (Fin n) ℝ => cavityRawComplement A B₀) :=
    (continuous_const.sub (continuous_id.matrix_mul continuous_id.matrix_transpose)).matrix_mul
      continuous_const
  simpa only [Function.comp_def, cavityRawComplement_eq E₀ B₀ hEB] using
    hc.tendsto E₀ |>.comp hE

end InvariantIsing

end

end OAI
