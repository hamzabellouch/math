import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalCappedGap

namespace OAI

/-! A fixed slab width threshold makes both actual transverse cutoff
losses smaller than half the oscillator gap. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ContinuumCoulomb

theorem verticalCutoffDerivativeBound_tendsto :
    Tendsto verticalCutoffDerivativeBound atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.const_mul (2:ℝ)).const_mul (Real.pi/2)
  have h' := h.mul_const verticalCutoffDerivativeConstant
  change Tendsto (fun S : ℝ => (Real.pi/2*(2/S))*verticalCutoffDerivativeConstant) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, zero_mul, mul_zero] using h'

theorem verticalCutoffLoss_tendsto {freq : ℝ} (hfreq : 0 < freq) :
    Tendsto (fun S : ℝ => verticalCutoffDerivativeBound S^2/2 +
      freq*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8)) atTop (𝓝 0) := by
  have harg : Tendsto (fun S : ℝ => (freq/8)*S^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop (by positivity : 0 < freq/8)
  have he : Tendsto (fun S : ℝ => Real.exp (-freq*S^2/8)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp harg using 1
    ext S
    congr 1
    ring
  simpa using ((verticalCutoffDerivativeBound_tendsto.pow 2).div_const 2).add
    (he.const_mul (freq*verticalCutoffTailConstant freq))

/-- The actual capped oscillator keeps a fixed positive excitation gap
for every sufficiently wide slab, uniformly over compact C1 tests. -/
theorem verticalCappedForm_uniform_complement_gap
    (hpublished : PublishedVerticalOscillatorGap) {freq : ℝ} (hfreq : 0 < freq) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ S : ℝ, R ≤ S → ∀ u : ℝ → ℝ,
      ContDiff ℝ 1 u → HasCompactSupport u →
      (∫ z, u z*verticalMode freq z) = 0 →
      freq*(∫ z, u z^2) ≤ verticalCappedForm freq S u := by
  have hbar : Tendsto (fun S : ℝ => (freq^2/8)*S^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop (by positivity : 0 < freq^2/8)
  have hb : ∀ᶠ S : ℝ in atTop, 3*freq/2 ≤ freq^2*S^2/8 := by
    filter_upwards [hbar.eventually (eventually_ge_atTop (3*freq/2))] with S hS
    convert hS using 1; ring
  have hl : ∀ᶠ S : ℝ in atTop, verticalCutoffDerivativeBound S^2/2 +
      freq*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8) < freq/2 :=
    (verticalCutoffLoss_tendsto hfreq).eventually (gt_mem_nhds (by linarith))
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 (hb.and hl)
  refine ⟨max 1 R, le_max_left _ _, fun S hS u hu hc ho => ?_⟩
  have hs : 0 < S := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hS)
  obtain ⟨hbarrier, hloss⟩ := hR S ((le_max_right _ _).trans hS)
  have h := verticalCappedForm_complement_lower hpublished hfreq hs hbarrier u hu hc ho
  have hm : 0 ≤ ∫ z, u z^2 := integral_nonneg (fun z => sq_nonneg _)
  have hcoef : freq ≤ 3*freq/2 - verticalCutoffDerivativeBound S^2/2 -
      freq*verticalCutoffTailConstant freq*Real.exp (-freq*S^2/8) := by linarith
  exact (mul_le_mul_of_nonneg_right hcoef hm).trans h

end ContinuumCoulomb

end

end OAI
