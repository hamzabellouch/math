import OAI.Probability.SLE.Loewner.HydrodynamicCoefficient

namespace OAI

/-! Elementary consequences of hydrodynamic normalization, including
the inverse coefficient and escape of the normalized inverse to infinity. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

lemma normalized_ratio_tendsto_cocompact {F : ℂ → ℂ}
    (hF : Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1)) :
    Tendsto F (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (cocompact ℂ) := by
  have hr : Tendsto (fun z : ℂ => ‖F z/z‖) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
    simpa only [norm_one] using hF.norm
  have hn := Filter.Tendsto.pos_mul_atTop (by norm_num : (0:ℝ)<1) hr
    (tendsto_norm_cocompact_atTop.mono_left (show cocompact ℂ ⊓ 𝓟 upperHalfPlane ≤ cocompact ℂ from inf_le_left))
  have hnorm : Tendsto (fun z : ℂ => ‖F z‖) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) atTop := by
    apply hn.congr'
    filter_upwards [(show ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 from
      (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact).filter_mono
      (show cocompact ℂ ⊓ 𝓟 upperHalfPlane ≤ cocompact ℂ from inf_le_left)] with z hz
    rw [norm_div,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]
  have hb := tendsto_norm_atTop_iff_cobounded.mp hnorm
  simpa only [Metric.cobounded_eq_cocompact] using hb

lemma inverse_hydrodynamic_coefficient {G F : ℂ → ℂ} {c : ℂ}
    (hG : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 c))
    (hF : Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1))
    (hGF : ∀ z ∈ upperHalfPlane, G (F z)=z) :
    Tendsto (fun z : ℂ => z*(F z-z)) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (-c)) := by
  have he := normalized_ratio_tendsto_cocompact hF
  have hq : Tendsto (fun z : ℂ => z/F z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
    simpa only [inv_div,inv_one] using hF.inv₀ one_ne_zero
  have ht := (hq.mul (hG.comp he)).neg
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [he.eventually ((isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact),
    (show ∀ᶠ z in cocompact ℂ ⊓ 𝓟 upperHalfPlane, z∈upperHalfPlane from
      eventually_inf_principal.mpr (Eventually.of_forall (fun _ h => h)))] with z hz hzH
  simp only [Function.comp_apply,hGF z hzH]
  have hz0 : F z ≠ 0 := hz
  field_simp [hz0]
  ring

end SLEExactGauge

end

end OAI
