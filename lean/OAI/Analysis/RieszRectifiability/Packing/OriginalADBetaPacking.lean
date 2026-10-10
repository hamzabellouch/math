import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.GlobalGrowth
import OAI.Analysis.RieszRectifiability.Flatness.BetaDescendantTotalMass

namespace OAI

/-!
# Bad-beta packing for the original AD hypotheses

For nontrivial support, AD regularity supplies global growth and converts the uniform
bad-descendant estimate to the original Riesz hypotheses. Subsingleton support has no positive
admissible core radius, so that branch follows directly from the diameter condition.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem original_AD_Riesz_bad_beta_total_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∑' i : BadBetaDescendant (p + 1) μ R hR k z H ε,
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  by_cases hsupport : μ.support.Nontrivial
  · obtain ⟨G, hg⟩ := globalGrowth_of_ADRegular_nontrivial (p + 1) μ hAD hsupport
    have hG : 0 < G + 1 := by linarith [hg.1]
    have hg' : GlobalUpperGrowth (p + 1) (G + 1) μ := hg.mono_constant (by linarith)
    obtain ⟨C, hC, hballs⟩ := hAD
    have hCpos : 0 < C := zero_lt_one.trans_le hC
    obtain ⟨D, hD⟩ := hRiesz
    obtain ⟨K, hK, hpack⟩ := exists_uniform_bad_beta_total_mass hnd C (G + 1) H ε D hCpos hG hH hε
    exact ⟨K, hK, hpack μ hg' (fun x hx r hr => (hballs x hx r hr).1) hD⟩
  · have hsub : μ.support.Subsingleton := Set.not_nontrivial_iff.mp hsupport
    refine ⟨1, by norm_num, ?_⟩
    intro R hR k z hcore
    have hdiam : ediam μ.support = 0 := ediam_eq_zero_iff.mpr hsub
    have hzero : ENNReal.ofReal (latticeRadius R k / 8) = 0 :=
      le_antisymm (hdiam ▸ hcore.2) (zero_le)
    exact ((ENNReal.ofReal_pos.mpr hcore.1).ne' hzero).elim

end

end RieszRectifiability

end OAI
