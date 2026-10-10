import OAI.Probability.SLE.Loewner.HydrodynamicComposition
import Mathlib.Topology.Algebra.Group.ContinuousDiv

namespace OAI

/-! Hydrodynamic normalization under the translated chart compositions
used for a future slit. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma complex_cocompact_eventually_ne_zero : ∀ᶠ z : ℂ in cocompact ℂ, z≠0 :=
  (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact

lemma normalized_ratio_escape {l : Filter ℂ} {F : ℂ → ℂ}
    (hl : l≤cocompact ℂ) (hF : Tendsto (fun z => F z/z) l (𝓝 1)) :
    Tendsto F l (cocompact ℂ) := by
  have hr : Tendsto (fun z => ‖F z/z‖) l (𝓝 1) := by
    simpa only [norm_one] using hF.norm
  have hn := Filter.Tendsto.pos_mul_atTop (by norm_num : (0:ℝ)<1) hr
    (tendsto_norm_cocompact_atTop.mono_left hl)
  have hnorm : Tendsto (fun z => ‖F z‖) l atTop := by
    apply hn.congr'
    filter_upwards [complex_cocompact_eventually_ne_zero.filter_mono hl]
      with z hz
    rw [norm_div,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hnorm

lemma complex_inv_tendsto_cocompact_zero :
    Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
  simpa only [Metric.cobounded_eq_cocompact] using
    (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))

theorem shifted_hydrodynamic_coefficient {G H : ℂ → ℂ} {c d : ℂ} (u : ℝ)
    (hG : Tendsto (fun z => z*(G z-z)) (cocompact ℂ) (𝓝 c))
    (hH : Tendsto (fun z => z*(H z-z)) (cocompact ℂ) (𝓝 d)) :
    Tendsto (fun z => z*((u:ℂ)+H (G z-(u:ℂ))-z)) (cocompact ℂ) (𝓝 (c+d)) := by
  have hu : Tendsto (fun z : ℂ => (u:ℂ)/z) (cocompact ℂ) (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using complex_inv_tendsto_cocompact_zero.const_mul (u:ℂ)
  have hs : Tendsto (fun z => (G z-(u:ℂ))/z) (cocompact ℂ) (𝓝 1) := by
    simpa only [sub_div,sub_zero] using (hydrodynamic_ratio_limit hG).sub hu
  have he := normalized_ratio_escape le_rfl hs
  have hq : Tendsto (fun z => z/(G z-(u:ℂ))) (cocompact ℂ) (𝓝 1) := by
    simpa only [inv_div,inv_one] using hs.inv₀ one_ne_zero
  have hh := (hq.mul (hH.comp he)).add hG
  rw [one_mul,add_comm d c] at hh
  apply hh.congr'
  filter_upwards [he.eventually ((isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact)]
    with z hz
  dsimp only [Function.comp_apply]
  field_simp [show G z-(u:ℂ)≠0 from hz]
  ring

lemma upper_translation_tendsto (u : ℝ) :
    Tendsto (fun z : ℂ => z+(u:ℂ)) (cocompact ℂ ⊓ 𝓟 upperHalfPlane)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) := by
  apply tendsto_inf.mpr
  constructor
  · exact (Homeomorph.addRight (u:ℂ)).isClosedEmbedding.tendsto_cocompact.mono_left inf_le_left
  · apply tendsto_principal.mpr
    rw [eventually_inf_principal]
    exact Eventually.of_forall fun z hz => by
      change 0<(z+(u:ℂ)).im
      simpa only [add_im,ofReal_im,add_zero] using (show 0<z.im from hz)

theorem shifted_inverse_normalized {F J : ℂ → ℂ} (u : ℝ)
    (hF : Tendsto (fun z => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1))
    (hJ : Tendsto (fun z => J z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1))
    (hJm : MapsTo J upperHalfPlane upperHalfPlane) :
    Tendsto (fun z => F ((u:ℂ)+J (z-(u:ℂ)))/z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
  have hshift := upper_translation_tendsto (-u)
  simp only [ofReal_neg,← sub_eq_add_neg] at hshift
  have hi := complex_inv_tendsto_cocompact_zero.mono_left
    (show cocompact ℂ ⊓ 𝓟 upperHalfPlane≤cocompact ℂ from inf_le_left)
  have hu : Tendsto (fun z : ℂ => (u:ℂ)/z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul (u:ℂ)
  have hratio : Tendsto (fun z : ℂ => (z-(u:ℂ))/z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℂ => (1:ℂ))
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1)).sub hu
    rw [sub_zero] at hh
    apply hh.congr'
    filter_upwards [complex_cocompact_eventually_ne_zero.filter_mono
      (show cocompact ℂ ⊓ 𝓟 upperHalfPlane≤cocompact ℂ from inf_le_left)] with z hz
    rw [sub_div,div_self (show z≠0 from hz)]
  have hJratio := (hJ.comp hshift).mul hratio
  have hmid : Tendsto (fun z : ℂ => ((u:ℂ)+J (z-(u:ℂ)))/z)
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
    have hh := hu.add hJratio
    simp only [zero_add,mul_one] at hh
    apply hh.congr'
    filter_upwards [(hshift.mono_right inf_le_left).eventually
      ((isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact)] with z hz
    dsimp only [Function.comp_apply]
    field_simp [show z-(u:ℂ)≠0 from hz]
  have hmidEscape := normalized_ratio_escape inf_le_left hmid
  have hmidUpper : Tendsto (fun z : ℂ => (u:ℂ)+J (z-(u:ℂ)))
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓟 upperHalfPlane) := by
    apply tendsto_principal.mpr
    rw [eventually_inf_principal]
    exact Eventually.of_forall fun z hz => by
      have hsub : z-(u:ℂ)∈upperHalfPlane := by
        simpa only [upperHalfPlane,mem_ofPred_eq,sub_im,ofReal_im,sub_zero] using hz
      simpa only [upperHalfPlane,mem_ofPred_eq,add_im,ofReal_im,zero_add] using hJm hsub
  have hh := (hF.comp (tendsto_inf.mpr ⟨hmidEscape,hmidUpper⟩)).mul hmid
  rw [mul_one] at hh
  apply hh.congr'
  filter_upwards [hmidEscape.eventually ((isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact)]
    with z hz
  dsimp only [Function.comp_apply]
  field_simp [show (u:ℂ)+J (z-(u:ℂ))≠0 from hz]

end SLEExactGauge

end

end OAI
