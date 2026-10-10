import OAI.Probability.InvariantIsing.Cavity.CavityFrameAlgebra

namespace OAI

/-! The correction used to orthonormalize a fixed number of Gaussian
columns converges to the identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_gram_sqrt_tendsto {q : ℕ} (G : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hG : ∀ n, (G n).PosSemidef) (hlim : Tendsto G atTop (𝓝 1)) :
    Tendsto (fun n => CFC.sqrt (G n)) atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hw : Tendsto G atTop (𝓝[{A : Matrix (Fin q) (Fin q) ℝ | 0 ≤ A}] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => (hG n).nonneg)⟩
  have hOne : (0 : Matrix (Fin q) (Fin q) ℝ) ≤ 1 := Matrix.PosSemidef.one.nonneg
  have hc := (CFC.continuousOn_sqrt (A := Matrix (Fin q) (Fin q) ℝ)).continuousWithinAt hOne
  have ht := hc.tendsto.comp hw
  change Tendsto (fun n => CFC.sqrt (G n)) atTop
    (𝓝 (CFC.sqrt (1 : Matrix (Fin q) (Fin q) ℝ))) at ht
  simpa only [CFC.sqrt_one] using ht

lemma cavity_gram_correction_tendsto {q : ℕ} (G : ℕ → Matrix (Fin q) (Fin q) ℝ)
    (hG : ∀ n, (G n).PosSemidef) (hlim : Tendsto G atTop (𝓝 1)) :
    Tendsto (fun n => (CFC.sqrt (G n))⁻¹) atTop
      (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hc : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℝ → _) 1 := by
    have hr : ContinuousAt (Ring.inverse : ℝ → ℝ) 1 := by
      simpa only [Units.val_one] using NormedRing.inverse_continuousAt (1 : ℝˣ)
    exact continuousAt_matrix_inv _ (by simpa only [Matrix.det_one] using hr)
  have ht := hc.tendsto.comp (cavity_gram_sqrt_tendsto G hG hlim)
  change Tendsto (fun n => (CFC.sqrt (G n))⁻¹) atTop
    (𝓝 ((1 : Matrix (Fin q) (Fin q) ℝ)⁻¹)) at ht
  simpa only [inv_one] using ht

theorem cavityGaussian_correction_tendsto (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun n => (CFC.sqrt (cavityEmpiricalGram x n))⁻¹) atTop
        (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  filter_upwards [cavityEmpiricalGram_tendsto q] with x hx
  exact cavity_gram_correction_tendsto (cavityEmpiricalGram x)
    (cavityEmpiricalGram_posSemidef x) hx

theorem cavityGaussian_normalized_gram_eventually (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q, ∀ᶠ n in atTop,
      (cavityNormalizeFrame (cavityGaussianMatrix x n)).transpose *
        cavityNormalizeFrame (cavityGaussianMatrix x n) = 1 := by
  filter_upwards [cavityEmpiricalGram_eventually_posDef q] with x hx
  filter_upwards [hx] with n hn
  apply cavityNormalizeFrame_gram
  rwa [cavityGaussianMatrix_gram]

end InvariantIsing

end

end OAI
