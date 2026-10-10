import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.CellRestartPacking
import OAI.Analysis.RieszRectifiability.Packing.OriginalADBetaPacking

namespace OAI

/-!
# Mass packing for bad-beta restart roots

For an AD-regular measure with an L²-bounded Riesz transform, the total mass of
restart roots triggered by large bilateral beta numbers is bounded by a constant
times the initial clean cell mass. The descendant packing estimate contributes
`K`, while the initial root contributes the additional `1`. The estimate retains
the admissibility condition on the initial cell's core radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem original_AD_Riesz_bad_beta_restart_mass {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℝ) (hR : 0 < R) (k : ℕ)
      (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ (latticeRadius R k / 8) →
      ∑' i : {i : SupportCellDescendant μ R hR k z // cellRestartsAfter
        (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius)) i},
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨K, hK, hpack⟩ := original_AD_Riesz_bad_beta_total_mass hnd μ hAD hRiesz H ε hH hε
  refine ⟨1 + K, by linarith, ?_⟩
  intro R hR k z hcore
  have h := restart_roots_total_mass_le μ R hR k z
    (fun q => ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius))
    (ENNReal.ofReal K) (hpack R hR k z hcore)
  simpa only [ENNReal.ofReal_add zero_le_one hK.le, ENNReal.ofReal_one] using! h

end

end RieszRectifiability

end OAI
