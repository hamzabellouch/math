import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningActionGrowth
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaleLimit

namespace OAI

/-! The forbidden action diverges along every escaping turning radius,
for any fixed inner radius and fixed Airy observation point. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_forbidden_action_tendsto
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      spectralLiouvilleSlope (eta n) (r₀ n)*(d n)^3 = 1) :
    Tendsto (fun n => (∫ t in R..(r₀ n-M*d n),
      spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t).re)
      atTop atTop := by
  have hd := spectralTurningScale_tendsto eta r₀ d hr₀
    (hdata.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩))
  have hlarge : ∀ᶠ n in atTop, (r₀ n)^2/64 ≤
      (∫ t in R..(r₀ n-M*d n),
        spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) t).re := by
    filter_upwards [hdata,hd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hr₀.eventually (eventually_ge_atTop (max (4*R) (2*M)))] with n hn hdn hrn
    have hdp : 0 < d n := by
      apply lt_of_le_of_ne hn.2.1
      intro he
      have hsc := hn.2.2.2.2
      rw [← he] at hsc
      norm_num at hsc
    exact spectralTurning_forbidden_action_lower h (b n) (eta n) (omega n) (gamma n)
      (r₀ n) R (r₀ n-M*d n) hn.2.2.1 hn.1 hR
      (by linarith [le_trans (le_max_left (4*R) (2*M)) hrn])
      (by nlinarith [le_trans (le_max_right (4*R) (2*M)) hrn])
      (by nlinarith) hn.2.2.2.1
  have hsq := (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hr₀
  have hbound : Tendsto (fun n => (r₀ n)^2/64) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) hsq
  rw [tendsto_atTop]
  intro A
  filter_upwards [hlarge,hbound.eventually (eventually_ge_atTop A)] with n hn hAn
  exact hAn.trans hn

end DefocusingNLS

end OAI
