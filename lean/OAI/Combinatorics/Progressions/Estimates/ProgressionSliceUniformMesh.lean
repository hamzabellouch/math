import OAI.Combinatorics.Progressions.Estimates.DenseProgressionInnerFamily

namespace OAI

section

namespace Erdos3

theorem progression_slice_uniform_mesh {L step H : ℕ} (c : ℤ)
    (hL : 0 < L) (hstep : 0 < step) {δ : ℝ} (hδ : 0 < δ)
    (hlarge : 2 ≤ δ * L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    2 ≤ H ∧ (step : ℝ) / L ≤ 4 / (δ * L) ∧
      ∀ M : ℕ, (M : ℝ) / H ≤ (M : ℝ) / (δ * L) := by
  rw [card_integerProgressionSupport c step H hstep] at hdense
  have hH : 2 ≤ H := by exact_mod_cast hlarge.trans hdense
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hδL : 0 < δ * L := lt_of_lt_of_le (by norm_num) hlarge
  have hgeom := progression_slice_endpoint_geometry c hL hstep hH hδ hsubset
    (by simpa only [card_integerProgressionSupport c step H hstep] using hdense)
  refine ⟨hH, hgeom.2.2.2.trans ?_, fun M => ?_⟩
  · apply (div_le_div_iff₀ (by linarith : 0 < (H : ℝ) - 1) hδL).mpr
    linarith
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg M) hδL hdense

theorem progression_slice_uniform_size {L step H d M : ℕ} (c : ℤ)
    (hstep : 0 < step) {δ : ℝ}
    (hlarge : (d * M : ℕ) ≤ δ * L)
    (hdense : δ * L ≤ ((integerProgressionSupport c (step : ℤ) H).card : ℝ)) :
    d * M ≤ H := by
  rw [card_integerProgressionSupport c step H hstep] at hdense
  exact_mod_cast hlarge.trans hdense

end Erdos3

end

end OAI
