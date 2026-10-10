import OAI.Probability.RadialTransition.PackingLimit

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

theorem canonical_support_supergradient {H Q : Pressure} {βc hc s ρ : ℝ}
    (hβc : 0 < βc)
    (hdual : ∀ β, 0 < β → H β ρ = sSup (Set.range fun h : ℝ => h * ρ - Q β h))
    (hs : pressureSupport Q βc hc s ρ) :
    ∀ β, 0 < β → H β ρ ≤ H βc ρ - s * (β - βc) := by
  have hbound (β : ℝ) (hβ : 0 < β) (h : ℝ) :
      h * ρ - Q β h ≤ hc * ρ - Q βc hc - s * (β - βc) := by
    have hh := hs β h hβ
    linarith
  have heq : H βc ρ = hc * ρ - Q βc hc := by
    rw [hdual βc hβc]
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨h, rfl⟩
      simpa using hbound βc hβc h
    · apply le_csSup
      · refine ⟨hc * ρ - Q βc hc, ?_⟩
        rintro _ ⟨h, rfl⟩
        simpa using hbound βc hβc h
      · exact ⟨hc, rfl⟩
  intro β hβ
  rw [hdual β hβ, heq]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨h, rfl⟩
  exact hbound β hβ h

theorem concave_oneSided_derivatives {H : ℝ → ℝ}
    (hH : ConcaveOn ℝ (Ioi 0) H) {β : ℝ} (hβ : 0 < β) :
    ∃ l r : ℝ, HasDerivWithinAt H l (Iic β) β ∧
      HasDerivWithinAt H r (Ici β) β := by
  have hx : β ∈ interior (Ioi (0 : ℝ)) := by simpa using hβ
  have hl := (hH.neg.hasDerivWithinAt_leftDeriv_of_mem_interior hx).neg.Iic_of_Iio
  have hr := (hH.neg.hasDerivWithinAt_rightDeriv_of_mem_interior hx).neg.Ici_of_Ioi
  exact ⟨_, _, by simpa using hl, by simpa using hr⟩

theorem supergradient_oneSided_bounds {H : ℝ → ℝ} {β m l r : ℝ}
    (hβ : 0 < β)
    (hm : ∀ y, 0 < y → H y ≤ H β + m * (y - β))
    (hl : HasDerivWithinAt H l (Iic β) β)
    (hr : HasDerivWithinAt H r (Ici β) β) : r ≤ m ∧ m ≤ l := by
  have hl' := (hasDerivWithinAt_iff_tendsto_slope' (s := Iio β) (by simp)).mp hl.Iio_of_Iic
  have hr' := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi β) (by simp)).mp hr.Ioi_of_Ici
  constructor
  · apply le_of_tendsto hr'
    filter_upwards [self_mem_nhdsWithin,
      (lt_mem_nhds hβ).filter_mono nhdsWithin_le_nhds] with y hy hy0
    rw [slope_def_field]
    apply (div_le_iff₀ (sub_pos.mpr hy)).mpr
    linarith [hm y hy0]
  · apply ge_of_tendsto hl'
    filter_upwards [self_mem_nhdsWithin,
      (lt_mem_nhds hβ).filter_mono nhdsWithin_le_nhds] with y hy hy0
    rw [slope_def_field]
    apply (le_div_iff_of_neg (sub_neg.mpr hy)).mpr
    linarith [hm y hy0]

theorem not_differentiable_of_oneSided_gap {f : ℝ → ℝ} {x l r : ℝ}
    (hl : HasDerivWithinAt f l (Iic x) x) (hr : HasDerivWithinAt f r (Ici x) x)
    (hgap : r < l) : ¬DifferentiableAt ℝ f x := by
  intro hd
  have hl' := hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic x)
  have hr' := hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici x)
  rw [hl.derivWithin (uniqueDiffWithinAt_Iic x)] at hl'
  rw [hr.derivWithin (uniqueDiffWithinAt_Ici x)] at hr'
  linarith

theorem canonical_corner_of_pressure_supports {H Q : Pressure}
    {βc hc s₁ s₂ ρ t : ℝ} (hβc : 0 < βc) (ht : 0 < t) (hs : s₁ < s₂)
    (hdual : ∀ β, 0 < β → H β ρ = sSup (Set.range fun h : ℝ => h * ρ - Q β h))
    (hconc : ConcaveOn ℝ (Ioi 0) (fun β => H β ρ))
    (hs₁ : pressureSupport Q βc hc s₁ ρ)
    (hs₂ : pressureSupport Q βc hc s₂ ρ) :
    StrictTemperatureCorner (fun β => t * H β ρ / β) βc := by
  obtain ⟨l, r, hl, hr⟩ := concave_oneSided_derivatives hconc hβc
  have hm₁ : ∀ β, 0 < β → H β ρ ≤ H βc ρ + (-s₁) * (β - βc) := by
    simpa only [neg_mul, sub_eq_add_neg] using canonical_support_supergradient hβc hdual hs₁
  have hm₂ : ∀ β, 0 < β → H β ρ ≤ H βc ρ + (-s₂) * (β - βc) := by
    simpa only [neg_mul, sub_eq_add_neg] using canonical_support_supergradient hβc hdual hs₂
  have hb₁ := supergradient_oneSided_bounds hβc hm₁ hl hr
  have hb₂ := supergradient_oneSided_bounds hβc hm₂ hl hr
  have hrl : r < l := by linarith
  have hleft := (hl.const_mul t).div (hasDerivAt_id βc).hasDerivWithinAt hβc.ne'
  have hright := (hr.const_mul t).div (hasDerivAt_id βc).hasDerivWithinAt hβc.ne'
  have hgap : (t * r * βc - t * H βc ρ * 1) / βc ^ 2 <
      (t * l * βc - t * H βc ρ * 1) / βc ^ 2 := by
    apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hβc)).mpr
    nlinarith [mul_lt_mul_of_pos_left hrl (mul_pos ht hβc)]
  refine ⟨_, _, hleft, hright, hgap, ?_⟩
  exact not_differentiable_of_oneSided_gap hleft hright hgap

end RadialTransition

end

end OAI
