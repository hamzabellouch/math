import OAI.Analysis.Pureness.Completion.CompletedRankClosure
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal
variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma nonUnitalRoot_inr (a : D) (ha : 0 ≤ a) (j : ℕ) :
    ((nonUnitalRoot a j : D) : Unitization ℂ D) = normalizedRoot (a : Unitization ℂ D) j := by
  have hi := NonUnitalStarAlgHom.isometry (Unitization.inrNonUnitalStarAlgHom ℂ D)
    Unitization.inr_injective
  have hn : ((nonUnitalNormalize a : D) : Unitization ℂ D) = normalizePositive (a : Unitization ℂ D) := by
    simp only [nonUnitalNormalize, normalizePositive, Unitization.inr_smul, Unitization.norm_inr]
  unfold nonUnitalRoot normalizedRoot
  rw [← hn]
  exact (nonUnital_nnrpow_map (Unitization.inrNonUnitalStarAlgHom ℂ D) hi.continuous
    (nonUnitalNormalize a) (nonUnitalNormalize_nonneg a ha) _ (by positivity)).symm

lemma nonUnitalRoot_nonneg (a : D) (j : ℕ) : 0 ≤ nonUnitalRoot a j := CFC.nnrpow_nonneg

lemma nonUnitalRoot_norm_le (a : D) (ha : 0 ≤ a) (j : ℕ) : ‖nonUnitalRoot a j‖ ≤ 1 := by
  rw [← Unitization.norm_inr (𝕜 := ℂ) (nonUnitalRoot a j)]
  rw [nonUnitalRoot_inr a ha]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg _ j)).mpr
    (normalizedRoot_le_one _ (Unitization.inr_nonneg_iff.mpr ha) j)

lemma nonUnitalRoot_mul_hereditary_tendsto (h c : D) (hh : 0 ≤ h)
    (hc : (c : Unitization ℂ D) ∈ hereditaryCarrier (h : Unitization ℂ D)) :
    Tendsto (fun j => nonUnitalRoot h j * c) atTop (𝓝 c) := by
  have hi := NonUnitalStarAlgHom.isometry (Unitization.inrNonUnitalStarAlgHom ℂ D)
    Unitization.inr_injective
  apply hi.isEmbedding.tendsto_nhds_iff.mpr
  change Tendsto (fun j => ((nonUnitalRoot h j * c : D) : Unitization ℂ D)) atTop (𝓝 (c : Unitization ℂ D))
  simp only [Unitization.inr_mul, nonUnitalRoot_inr h hh]
  exact
    normalizedRoot_mul_hereditary_tendsto (h : Unitization ℂ D)
      (Unitization.inr_nonneg_iff.mpr hh) (c : Unitization ℂ D) hc
end CuntzPureness

end

end OAI
