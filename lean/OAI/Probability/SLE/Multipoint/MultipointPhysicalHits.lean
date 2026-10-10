import OAI.Probability.SLE.Multipoint.MultipointRadiusStatus

namespace OAI

/-! The finite-radius-stop event is exactly the physical conformal-radius
hit event in the original conformal domain. -/

noncomputable section
open Set Filter
open scoped NNReal ENNReal

namespace SLEExactGauge

private lemma physical_radius_level_value
    (J : ℂ → ℂ) (z : ℂ) (R e : ℝ) (hR : 0 < R) (he : 0 < e)
    (hRdef : R = 2*z.im*‖deriv J z‖) :
    ‖deriv J z‖ * ((2*z.im)*Real.exp (-Real.log (R/e))) = e := by
  have hexp : Real.exp (-Real.log (R/e)) = e/R := by
    rw [Real.exp_neg, Real.exp_log (div_pos hR he)]
    field_simp [hR.ne',he.ne']
  have hcoef : ‖deriv J z‖*(2*z.im) = R := by rw [hRdef]; ring
  rw [hexp,← mul_assoc,hcoef]
  field_simp [hR.ne']

theorem physical_radius_eq_hit_iff_finite_level
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (J : ℂ → ℂ) (z : ℂ) (R e : ℝ) (hR : 0 < R) (he : 0 < e)
    (hRdef : R = 2*z.im*‖deriv J z‖) :
    (∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧ physicalConformalRadius J G t z = e) ↔
      radiusLevelTime γ G z (Real.log (R/e)) < ⊤ := by
  have hc : 0 < ‖deriv J z‖ := by
    by_contra hn
    have hz : ‖deriv J z‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    rw [hz,mul_zero] at hRdef
    linarith
  have htarget := physical_radius_level_value J z R e hR he hRdef
  constructor
  · rintro ⟨t,ht,htR⟩
    have hfull : fullRadius G t z = (2*z.im)*Real.exp (-Real.log (R/e)) :=
      (mul_left_cancel₀ hc.ne') (htR.trans htarget.symm)
    rw [radiusLevelTime_eq_of_live_level hU hw z (Real.log (R/e)) t ht hfull]
    exact ENNReal.coe_lt_top
  · intro hf
    obtain ⟨t,ht,htR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z (Real.log (R/e)) hf
    exact ⟨t,ht,by rw [physicalConformalRadius,htR]; exact htarget⟩

theorem physical_radius_hit_iff_finite_level
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (J : ℂ → ℂ) (z : ℂ) (R e : ℝ) (hR : 0 < R) (he : 0 < e) (heR : e ≤ R)
    (hRdef : R = 2*z.im*‖deriv J z‖) :
    (∃ t : ℝ≥0, z ∈ survivingDomain γ t ∧ physicalConformalRadius J G t z ≤ e) ↔
      radiusLevelTime γ G z (Real.log (R/e)) < ⊤ := by
  constructor
  · rintro ⟨t,ht,htR⟩
    rcases lt_or_eq_of_le htR with hlt | heq
    · have hc : 0 < ‖deriv J z‖ := by
        by_contra hn
        have hz : ‖deriv J z‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
        rw [hz,mul_zero] at hRdef
        linarith
      have hlog : 0 ≤ Real.log (R/e) := Real.log_nonneg
        ((le_div_iff₀ he).mpr (by simpa only [one_mul] using heR))
      have htarget := physical_radius_level_value J z R e hR he hRdef
      apply radiusLevelTime_finite_of_live_radius_lt hU hw z (Real.log (R/e)) hlog t ht
      apply (mul_lt_mul_iff_right₀ hc).mp
      exact hlt.trans_eq htarget.symm
    · exact (physical_radius_eq_hit_iff_finite_level hU hw J z R e hR he hRdef).mp
        ⟨t,ht,heq⟩
  · intro hf
    obtain ⟨t,ht,hR⟩ := (physical_radius_eq_hit_iff_finite_level hU hw J z R e hR he hRdef).mpr hf
    exact ⟨t,ht,hR.le⟩

end SLEExactGauge

end

end OAI
