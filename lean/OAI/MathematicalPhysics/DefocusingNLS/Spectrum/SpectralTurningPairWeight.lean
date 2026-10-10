import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningWeightEscape

namespace OAI

/-! A single weight floor works for both turning channels. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralTurning_pair_floor (dp dm : ℝ) (hp : 0 < dp) (hm : 0 < dm) :
    (Real.sqrt (dp+dm))⁻¹ ≤ (Real.sqrt dp)⁻¹ ∧
      (Real.sqrt (dp+dm))⁻¹ ≤ (Real.sqrt dm)⁻¹ := by
  exact ⟨inv_anti₀ (Real.sqrt_pos.mpr hp) (Real.sqrt_le_sqrt (by linarith)),
    inv_anti₀ (Real.sqrt_pos.mpr hm) (Real.sqrt_le_sqrt (by linarith))⟩

theorem spectralTurning_pair_floor_tendsto (dp dm : ℕ → ℝ)
    (hp : Tendsto dp atTop (𝓝 0)) (hm : Tendsto dm atTop (𝓝 0))
    (hpp : ∀ᶠ n in atTop, 0 < dp n) (hmp : ∀ᶠ n in atTop, 0 < dm n) :
    Tendsto (fun n => (Real.sqrt (dp n+dm n))⁻¹) atTop atTop := by
  apply spectralTurning_weight_floor_tendsto
  · simpa only [add_zero] using hp.add hm
  · filter_upwards [hpp,hmp] with n hn hn'
    exact add_pos hn hn'

end DefocusingNLS

end OAI
