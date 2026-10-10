import OAI.Analysis.Mahler.FiberEndpoint

namespace OAI

/-! Polar preimage limits along the vertical fibers. -/

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

theorem fiberAngle_tendsto_pi {q r₀ : ℝ} (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hqneg : q < 0) (hq : radialMap r₀ = |q|) :
    Tendsto (fiberAngle q) (𝓝[>] r₀) (𝓝 Real.pi) := by
  have ht := fiberAngle_tendsto_zero (q := -q) hr₀ hr₁ (by linarith) (by simpa using hq)
  have hn : Tendsto (fun r => Real.pi - fiberAngle (-q) r) (𝓝[>] r₀) (𝓝 Real.pi) := by
    simpa using tendsto_const_nhds.sub ht
  apply hn.congr'
  filter_upwards [eventually_fiberDomain hr₀.le hr₁ hq] with r hr
  rw [fiberAngle_neg hr]
  ring

/-- The sign convention includes q=0 without imposing an angle at radius zero. -/
theorem fiberPreimage_tendsto_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) :
    Tendsto (fun r => polar r (fiberAngle q r)) (𝓝[>] r₀)
      (𝓝 (if 0 ≤ q then (r₀ : ℂ) else -(r₀ : ℂ))) := by
  have hrad : Tendsto (fun r : ℝ => r) (𝓝[>] r₀) (𝓝 r₀) := nhdsWithin_le_nhds
  rcases hr₀.eq_or_lt with hz | hrpos
  · subst r₀
    have hn : Tendsto (fun r : ℝ => ‖polar r (fiberAngle q r)‖) (𝓝[>] 0) (𝓝 0) := by
      simpa [polar, Complex.norm_exp] using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa using tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hc : Continuous (fun p : ℝ × ℝ => polar p.1 p.2) := by unfold polar; fun_prop
  by_cases hp : 0 ≤ q
  · rw [ite_eq_left hp]
    have ht := fiberAngle_tendsto_zero hrpos hr₁ hp hq
    simpa only [Function.comp_def, polar_zero] using
      (hc.tendsto (r₀,0)).comp (hrad.prodMk_nhds ht)
  · rw [ite_eq_right hp]
    have ht := fiberAngle_tendsto_pi hrpos hr₁ (lt_of_not_ge hp) hq
    simpa only [Function.comp_def, polar_pi] using
      (hc.tendsto (r₀,Real.pi)).comp (hrad.prodMk_nhds ht)

end SymmetricMahler

end

end OAI
