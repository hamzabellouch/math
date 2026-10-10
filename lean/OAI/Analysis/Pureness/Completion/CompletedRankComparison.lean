import OAI.Analysis.Pureness.Completion.CompletedHereditaryWeight

namespace OAI

noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
local notation "D" => CornerCompletion A
local notation "U" => Unitization ℂ (CornerCompletion A)

lemma completedWeight_le_rank_of_unitized_cuntz (τ : TracialState A) (c h : D)
    (_hc : 0 ≤ c) (hh : 0 ≤ h) (hc1 : ‖c‖ ≤ 1)
    (hch : CuntzSubequiv (c : U) (h : U)) :
    completedDiagonalWeight τ c ≤ completedRootRank τ h := by
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence (c : U) (h : U)).mp hch
  let y : ℕ → D := fun j => (((CFC.sqrt h : D) : U) * v j).snd
  have hy (j : ℕ) : (y j : U) = ((CFC.sqrt h : D) : U) * v j := by
    apply Unitization.ext
    · simp [y]
    · rfl
  have hs (j : ℕ) : ((star (y j) * y j : D) : U) = star (v j) * (h : U) * v j := by
    rw [Unitization.inr_mul, Unitization.inr_star, hy, star_mul]
    simp only [← Unitization.inr_star, (CFC.sqrt_nonneg h).star_eq, mul_assoc,
      ← mul_assoc (((CFC.sqrt h : D) : U)), ← Unitization.inr_mul,
      CFC.sqrt_mul_sqrt_self h hh]
  have ht : Tendsto (fun j => star (y j) * y j) atTop (𝓝 c) := by
    apply (Unitization.isometry_inr (𝕜 := ℂ)).isEmbedding.tendsto_nhds_iff.mpr
    change Tendsto (fun j => ((star (y j) * y j : D) : U)) atTop (𝓝 (c : U))
    simpa only [hs] using hv
  let d : ℕ → ℝ := fun j => max 1 ‖star (y j) * y j‖
  have hd (j : ℕ) : 0 < d j := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hdlim : Tendsto d atTop (𝓝 1) := by
    simpa only [max_eq_left hc1] using (tendsto_const_nhds (x := (1 : ℝ))).max ht.norm
  have hlim : Tendsto (fun j => (d j)⁻¹ • (star (y j) * y j)) atTop (𝓝 c) := by
    simpa only [inv_one, one_smul] using (hdlim.inv₀ one_ne_zero).smul ht
  apply completedDiagonalWeight_le_of_tendsto τ hlim
  intro j
  have hnorm : ‖y j * star (y j)‖ = ‖star (y j) * y j‖ := by
    rw [CStarRing.norm_self_mul_star, CStarRing.norm_star_mul_self]
  have hcontract : ‖(d j)⁻¹ • (y j * star (y j))‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hd j)), hnorm]
    exact (inv_mul_le_one₀ (hd j)).mpr (le_max_right _ _)
  have hmem : (((d j)⁻¹ • (y j * star (y j)) : D) : U) ∈ hereditaryCarrier (h : U) := by
    have hm : ((y j * star (y j) : D) : U) ∈ hereditaryCarrier (h : U) := by
      rw [Unitization.inr_mul, Unitization.inr_star, hy, star_mul, ← Unitization.inr_star,
        (CFC.sqrt_nonneg h).star_eq, ← Unitization.sqrt_inr]
      have he : CFC.sqrt (h : U) * v j * (star (v j) * CFC.sqrt (h : U)) =
          CFC.sqrt (h : U) * (v j * star (v j)) * CFC.sqrt (h : U) := by
        simp only [mul_assoc]
      rw [he]
      exact sqrt_sandwich_mem_hereditary _ _ (Unitization.inr_nonneg_iff.mpr hh)
    rw [Unitization.inr_smul]
    exact (hereditarySubalgebra (h : U) (Unitization.inr_nonneg_iff.mpr hh)).smul_mem (d j)⁻¹ hm
  calc
    _ = completedDiagonalWeight τ ((d j)⁻¹ • (y j * star (y j))) := by
      rw [completedDiagonalWeight_smul τ _ (le_of_lt (inv_pos.mpr (hd j))),
        completedDiagonalWeight_smul τ _ (le_of_lt (inv_pos.mpr (hd j))),
        completedDiagonalWeight_tracial]
    _ ≤ completedRootRank τ h := completedWeight_le_rank_of_hereditary τ h _ hh
      (smul_nonneg (le_of_lt (inv_pos.mpr (hd j))) (mul_star_self_nonneg _)) hcontract hmem

theorem completedRootRank_le_of_unitized_cuntz (τ : TracialState A) (a b : D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : CuntzSubequiv (a : U) (b : U)) :
    completedRootRank τ a ≤ completedRootRank τ b := by
  apply iSup_le
  intro j
  apply completedWeight_le_rank_of_unitized_cuntz τ _ b (nonUnitalRoot_nonneg a j) hb
    (nonUnitalRoot_norm_le a ha j)
  rw [nonUnitalRoot_inr a ha]
  exact (hereditary_cuntzSubequiv (a : U) (normalizedRoot (a : U) j)
    (Unitization.inr_nonneg_iff.mpr ha) (normalizedRoot_nonneg _ j)
    (normalizedRoot_mem_hereditary (Unitization.inr_nonneg_iff.mpr ha)
      (self_mem_hereditary _ (Unitization.inr_nonneg_iff.mpr ha))
      (Unitization.inr_nonneg_iff.mpr ha) j)).trans hab
end CuntzPureness

end

end OAI
