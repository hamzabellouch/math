import OAI.Analysis.StrictMeans.Spectrum

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

/-- A single, strictly positive gap works for every normalized univalent map,
and hence for the supremum of the individual bounded-map exponents. -/
theorem uniform_inverse_first_power_gap :
    ∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < C ∧
      (∀ (f : ℂ → ℂ), NormalizedUnivalent f →
        ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
          integralMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε)) ∧
      boundedSpectrum (-1) ≤ ((1 / 4 - ε : ℝ) : EReal) := by
  let b := (dyadicExponent+1/4)/2
  have hb : dyadicExponent < b := by dsimp [b]; linarith [dyadicExponent_lt_quarter]
  have hb0 : 0 < b := lt_of_le_of_lt dyadicExponent_nonneg hb
  have hb1 : b < 1/4 := by dsimp [b]; linarith [dyadicExponent_lt_quarter]
  obtain ⟨C,hC,hbound⟩ := uniform_integralMean_bound_above_dyadicExponent hb
  refine ⟨1/4-b,C,by linarith,by linarith,hC,?_,?_⟩
  · intro f hf r hr0 hr
    simpa only [show -(1/4:ℝ)+(1/4-b) = -b by ring] using hbound f hf r hr0 hr
  · rw [show (1/4:ℝ) - (1/4-b) = b by ring]
    apply iSup_le
    intro f
    apply iSup_le
    intro hf
    exact growthExponent_le_of_mean_bound f hf.1 hC (hbound f hf.1)

theorem uniform_inverse_first_power :
    ∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ (f : ℂ → ℂ), NormalizedUnivalent f →
        ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
          integralMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε) := by
  obtain ⟨ε,C,hε,hε',_hC,hbound,_hs⟩ := uniform_inverse_first_power_gap
  exact ⟨ε,C,hε,hε',hbound⟩

theorem bounded_spectrum_strict : boundedSpectrum (-1) < (1 / 4 : EReal) := by
  obtain ⟨ε,_C,hε,_hε',_hC,_hbound,hs⟩ := uniform_inverse_first_power_gap
  apply hs.trans_lt
  change ((1/4-ε : ℝ) : EReal) < ((1/4 : ℝ) : EReal)
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

theorem kraetzer_identity_false :
    ¬ ∀ p : ℝ, boundedSpectrum p = kraetzerPrediction p := by
  intro h
  have hp := bounded_spectrum_strict
  rw [h (-1)] at hp
  have hpred : kraetzerPrediction (-1) = ((1/4 : ℝ) : EReal) := by
    norm_num [kraetzerPrediction]
  rw [hpred] at hp
  change ((1/4 : ℝ) : EReal) < ((1/4 : ℝ) : EReal) at hp
  exact lt_irrefl _ hp

end
end StrictInverseFirstPower

end

end OAI
