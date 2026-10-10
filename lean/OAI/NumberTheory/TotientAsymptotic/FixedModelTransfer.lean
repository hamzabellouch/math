import OAI.NumberTheory.TotientAsymptotic.BandExtraction

namespace OAI

/-! The five-percent Ford interval lies inside the ten-percent model
interval once the uniform center ratio is sufficiently close to one. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem fixed_model_band_failure_transfer : ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ,i < m x → ∀ u : ℝ,
    (u < (9/10:ℝ)*bandScale x i ∨ (11/10:ℝ)*bandScale x i < u) →
    (u < (19/20:ℝ)*fordBandScale x i ∨ (21/20:ℝ)*fordBandScale x i < u) := by
  filter_upwards [fordBandScale_uniform_comparison (ε:=1/25) (by norm_num)] with x hx
  intro i hi u hu
  have hs := bandScale_pos hi
  have hr := abs_lt.mp (hx i hi)
  have hlo : (24/25:ℝ)*bandScale x i < fordBandScale x i := by
    have hh := (lt_div_iff₀ hs).mp (show (24/25:ℝ) < fordBandScale x i/bandScale x i by linarith only [hr.1])
    linarith only [hh]
  have hhi : fordBandScale x i < (26/25:ℝ)*bandScale x i := by
    have hh := (div_lt_iff₀ hs).mp (show fordBandScale x i/bandScale x i < (26/25:ℝ) by linarith only [hr.2])
    linarith only [hh]
  rcases hu with hu|hu
  · left
    nlinarith only [hu,hlo,hs]
  · right
    nlinarith only [hu,hhi,hs]

end TotientAsymptotic

end

end OAI
