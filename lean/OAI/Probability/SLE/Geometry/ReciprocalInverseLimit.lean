import OAI.Probability.SLE.Loewner.SlitInverseGerm

namespace OAI

/-! A germ tangent to the identity gives a normalized inverse chart at
infinity after conjugate inversion. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

lemma conjugateInversion_ne_zero {z : ℂ} (hz : z ≠ 0) : conjugateInversion z ≠ 0 := by
  change (conj z)⁻¹ ≠ 0
  apply inv_ne_zero
  intro he
  apply hz
  simpa only [conj_conj,map_zero] using congrArg conj he

lemma conjugateInversion_tendsto_zero :
    Tendsto conjugateInversion (cocompact ℂ) (𝓝 (0:ℂ)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  convert! (Complex.continuous_conj.tendsto 0).comp hi using 1
  · ext z
    simp only [Function.comp_apply,conjugateInversion,map_inv₀]
  · simp

lemma conjugateInversion_tendsto_punctured_zero :
    Tendsto conjugateInversion (cocompact ℂ) (𝓝[≠] (0:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨conjugateInversion_tendsto_zero,?_⟩
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  exact conjugateInversion_ne_zero hz

lemma conjugateInversion_ratio {r : ℂ → ℂ} (z : ℂ) :
    conjugateInversion (r (conjugateInversion z))/z =
      conj ((r (conjugateInversion z)/conjugateInversion z)⁻¹) := by
  change (conj (r (conjugateInversion z)))⁻¹/z =
    conj ((r (conjugateInversion z)/(conj z)⁻¹)⁻¹)
  rw [inv_div,map_div₀,map_inv₀,conj_conj]
  simp only [div_eq_mul_inv]
  ring

lemma reciprocal_inverse_tendsto_ratio {r : ℂ → ℂ}
    (hr : HasDerivAt r 1 0) (hr0 : r 0=0) :
    Tendsto (fun z : ℂ => conjugateInversion (r (conjugateInversion z))/z)
      (cocompact ℂ) (𝓝 1) := by
  have hs : Tendsto (fun w : ℂ => r w/w) (𝓝[≠] 0) (𝓝 1) := by
    convert! hr.tendsto_slope using 1
    ext w
    simp only [slope_def_field,hr0,sub_zero]
  have ht := (hs.comp conjugateInversion_tendsto_punctured_zero).inv₀ one_ne_zero
  have hc := (Complex.continuous_conj.tendsto (1:ℂ)⁻¹).comp ht
  simp only [inv_one,map_one] at hc
  apply hc.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  exact (conjugateInversion_ratio (r := r) z).symm

end SLEExactGauge

end

end OAI
