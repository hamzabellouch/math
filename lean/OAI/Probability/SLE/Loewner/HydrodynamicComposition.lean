import OAI.Probability.SLE.Loewner.HydrodynamicAsymptotics

namespace OAI

/-! The coefficient of a normalized composition subtracts capacities.
Schwarz–Pick then makes capacity monotone under inclusion of slit domains. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

lemma hydrodynamic_ratio_limit {G : ℂ → ℂ} {c : ℂ}
    (hG : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 c)) :
    Tendsto (fun z : ℂ => G z/z) (cocompact ℂ) (𝓝 1) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  have hh := (hG.mul (hi.pow 2)).const_add 1
  simp only [zero_pow two_ne_zero,mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := hz
  field_simp [hz0]
  ring

lemma hydrodynamic_composition_coefficient {G H F : ℂ → ℂ} {c d : ℂ}
    (hG : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 c))
    (hH : Tendsto (fun z : ℂ => z*(H z-z)) (cocompact ℂ) (𝓝 d))
    (hF : Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1))
    (hHF : ∀ z ∈ upperHalfPlane, H (F z)=z) :
    Tendsto (fun z : ℂ => z*(G (F z)-z)) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (c-d)) := by
  have hescape := normalized_ratio_tendsto_cocompact hF
  have hquot : Tendsto (fun z : ℂ => z/F z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
    simpa only [inv_div,inv_one] using hF.inv₀ one_ne_zero
  have hh := (hquot.mul (hG.comp hescape)).add (inverse_hydrodynamic_coefficient hH hF hHF)
  simp only [one_mul,sub_eq_add_neg] at hh ⊢
  apply hh.congr'
  filter_upwards [hescape.eventually ((isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact)] with z hz
  simp only [Function.comp_apply]
  have hz0 : F z ≠ 0 := hz
  field_simp [hz0]
  ring

lemma hydrodynamic_composition_ratio {G F : ℂ → ℂ} {c : ℂ}
    (hG : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 c))
    (hF : Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1)) :
    Tendsto (fun z : ℂ => G (F z)/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1) := by
  have he := normalized_ratio_tendsto_cocompact hF
  have hh := ((hydrodynamic_ratio_limit hG).comp he).mul hF
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [he.eventually ((isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact)] with z hz
  simp only [Function.comp_apply]
  have hz0 : F z ≠ 0 := hz
  field_simp [hz0]


lemma normalized_selfMap_coefficient_nonpos {G : ℂ → ℂ} {c : ℝ}
    (hd : DifferentiableOn ℂ G upperHalfPlane) (hm : MapsTo G upperHalfPlane upperHalfPlane)
    (hc : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (c:ℂ)))
    (hn : Tendsto (fun z : ℂ => G z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1)) : c≤0 := by
  have hr := Complex.continuous_re.tendsto (c:ℂ) |>.comp (hc.comp verticalInfinity_tendsto)
  have hh : ∀ᶠ n in atTop, (verticalInfinity n*(G (verticalInfinity n)-verticalInfinity n)).re ≤ 0 := by
    apply Eventually.of_forall
    intro n
    have hheight := normalized_halfPlane_height hd hm hn (verticalInfinity_mem n)
    have hy : 0 < (n:ℝ)+1 := by positivity
    simp only [verticalInfinity,mul_im,mul_re,ofReal_re,ofReal_im,I_re,I_im,mul_zero,
      add_zero,mul_one,sub_im,sub_re,zero_sub] at hheight ⊢
    nlinarith
  have hle : (c:ℂ).re ≤ 0 := le_of_tendsto hr (by
    simpa only [Function.comp_apply] using hh)
  simpa only [ofReal_re] using hle

theorem nested_hydrodynamic_coefficient_le
    {D : Set ℂ} {G H F : ℂ → ℂ} {c d : ℝ}
    (hG : DifferentiableOn ℂ G D) (hGm : MapsTo G D upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hFm : MapsTo F upperHalfPlane D)
    (hc : Tendsto (fun z : ℂ => z*(G z-z)) (cocompact ℂ) (𝓝 (c:ℂ)))
    (hd : Tendsto (fun z : ℂ => z*(H z-z)) (cocompact ℂ) (𝓝 (d:ℂ)))
    (hn : Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1))
    (hHF : ∀ z ∈ upperHalfPlane, H (F z)=z) : c≤d := by
  have hcomp := hydrodynamic_composition_coefficient hc hd hn hHF
  have hnorm := hydrodynamic_composition_ratio hc hn
  have hle := normalized_selfMap_coefficient_nonpos (hG.comp hF hFm)
    (hGm.comp hFm) (c := c-d) (by
      convert! hcomp using 1
      simp only [ofReal_sub])
    (by convert! hnorm using 1)
  linarith

end SLEExactGauge

end

end OAI
